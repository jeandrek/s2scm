;;;; S2scm--Scheme compiler for Scratch

;;;; Much of this work is a derivative of Structure and Interpretation of
;;;; Computer Programs by Abelson, Sussman, and Sussman, at
;;;; https://mitpress.mit.edu/sites/default/files/sicp/index.html, which is
;;;; under the Creative Commons Attribution-ShareAlike 4.0 International
;;;; License.  S2scm is free software and under the same license.  To view a
;;;; copy of this license, visit http://creativecommons.org/licenses/by-sa/4.0/
;;;; or send a letter to Creative Commons, PO Box 1866, Mountain View, CA
;;;; 94042, USA.

;;; Todo:

;;; o Perhaps write JavaScript program to generate JSON files from runtime
;;;   environment project.

;;; o Add graphics and sound blocks.

;;; o Don't save state redundantly.

;;; o Don't type check redundantly.  This will probably require returning the
;;;   environment from the code-generation procedures.  (Once that is done,
;;;   making LETREC and DEFINE error at compile time will be trivial.)

;;; o Add strings, input and output, and possibly metacircular evaluator.

;;; o Allow quotation of lists, QUASIQUOTE, and possibly CASE.

(define (interactive-compile-loop output-file-name)
  (let ((env (make-scheme-environment)))
    (let loop ()
      (display ";;; Compile expression to ")
      (display output-file-name)
      (display ":")
      (newline)
      (let ((exp (read)))
	(write-compiled-program-to-file output-file-name (compile exp env))
	(loop)))))

(define (compile-files output-file-name . input-file-names)
  (write-compiled-program-to-file
   output-file-name
   (compile-program (flatmap read-source-file input-file-names)
		    (make-scheme-environment))))

(define (read-source-file file-name)
  (call-with-input-file
   file-name
   (lambda (port)
     (let helper ()
       (let ((obj (read port)))
	 (if (eof-object? obj)
	     '()
	     (cons obj (helper))))))))

(define (write-compiled-program-to-file output-file-name program)
  (call-with-output-file
   output-file-name
   (lambda (port)
     (define (copy-input input-port)
       (let ((obj (read-char input-port)))
	 (if (not (eof-object? obj))
	     (begin (write-char obj port)
		    (copy-input input-port)))))
     (call-with-input-file "prologue.json" copy-input)
     (do ((program program (cdr program)))
	 ((null? program))
       (write-char #\, port)
       (display-json (car program) port))
     (call-with-input-file "epilogue.json" copy-input))))

(define (compile-program program env)
  (compile (program->expression program env) env))

(define (compile exp env)
  (set! *label-counter* 0)
  (let* ((basic-blocks
	  (intermediate->basic-blocks (compile-with-labels exp env #t)))
	 (k (vector-length basic-blocks)))
    (generate-script (basic-blocks->scratch basic-blocks 1 k) k)))


;;; The Scheme environment

(define (make-scheme-environment)
  (let ((compilers
	 (list (cons 'quote (lambda (exp env tail?)
			      (compile-datum (quoted-datum exp))))
	       (cons 'lambda compile-lambda)
	       (cons 'if compile-if)
	       (cons 'let compile-let)
	       (cons 'begin (lambda (exp env tail?)
			      (compile-sequence (begin-actions exp) env tail?)))
	       (cons 'set! compile-assignment)))
	(transformers
	 (list (cons 'cond expand-cond)
	       (cons 'and expand-and)
	       (cons 'or expand-or)
	       (cons 'let* expand-let*)
	       (cons 'letrec expand-letrec)
	       (cons 'do expand-do)
	       (cons 'delay expand-delay)))
	(primitives (make-primitives)))
    (extend-with-special-forms-and-primitives
     (append
      (map (lambda (pair) (cons (car pair) (make-special-form (cdr pair))))
	   compilers)
      (map (lambda (pair) (cons (car pair) (make-derived-form (cdr pair))))
	   transformers)
      primitives)
     the-empty-environment)))

(define (make-derived-form transformer)
  (make-special-form
   (lambda (exp env tail?) (compile-with-labels (transformer exp) env tail?))))


;;; Source transformations

(define (program->expression program env)
  (let loop ((variables '())
	     (bindings '())
	     (exps '())
	     (program program))
    (cond ((null? program) (make-let bindings (reverse exps)))
	  ((definition? (car program))
	   (let ((var (definition-variable (car program)))
		 (val (definition-value (car program))))
	     (cond ((memq var variables)
		    (loop variables bindings
			  (cons (make-assignment var val) exps) (cdr program)))
		   ((bound? var env)
		    (loop (cons var variables)
			  (cons (make-let-binding var var) bindings)
			  (cons (make-assignment var val) exps) (cdr program)))
		   (else
		    (loop (cons var variables)
			  (cons (make-let-binding var unassigned) bindings)
			  (cons (make-assignment var val) exps)
			  (cdr program))))))
	  (else
	   (loop variables bindings (cons (car program) exps) (cdr program))))))

(define (scan-out-definitions body)
  (if (not (definition? (car body)))
      body
      (let loop ((bindings '())
		 (body body))
	(if (not (definition? (car body)))
	    (list (make-letrec bindings body))
	    (loop (cons (make-let-binding (definition-variable (car body))
					  (definition-value (car body)))
			bindings)
		  (cdr body))))))

(define (expand-cond exp)
  (let helper ((clauses (cond-clauses exp)))
    (let ((clause (car clauses)))
      (cond ((null? (cdr clauses))
	     (cond ((cond-else? clause)
		    (make-begin (cond-body clause)))
		   ((cond-procedure? clause)
		    (let ((var (generate-variable)))
		      (make-let
		       (list (make-let-binding var (cond-predicate clause)))
		       (list
			(make-if
			 var
			 (make-application (cond-recipient clause)
					   (list var)))))))
		   ((null? (cond-body clause))
		    (cond-predicate clause))
		   (else
		    (make-if (cond-predicate clause)
			     (make-begin (cond-body clause))))))
	    ((cond-procedure? clause)
	     (let ((var (generate-variable)))
	       (make-let
		(list (make-let-binding var (cond-predicate clause)))
		(list
		 (make-if var
			  (make-application (cond-recipient clause) (list var))
			  (helper (cdr clauses)))))))
	    ((null? (cond-body clause))
	     (let ((var (generate-variable)))
	       (make-let
		(list (make-let-binding var (cond-predicate clause)))
		(list (make-if var var (helper (cdr clauses)))))))
	    (else
	     (make-if (cond-predicate clause)
		      (make-begin (cond-body clause))
		      (helper (cdr clauses))))))))

(define (expand-and exp)
  (let helper ((tests (and-tests exp)))
    (cond ((null? tests) #t)
	  ((null? (cdr tests)) (car tests))
	  (else (make-if (car tests) (helper (cdr tests)) #f)))))

(define (expand-or exp)
  (let helper ((tests (or-tests exp)))
    (cond ((null? tests) #f)
	  ((null? (cdr tests)) (car tests))
	  (else
	   (let ((var (generate-variable)))
	     (make-let (list (make-let-binding var (car tests)))
		       (list (make-if var var (helper (cdr tests))))))))))

(define (expand-named-let exp)
  (let ((var (named-let-variable exp))
	(bindings (named-let-bindings exp)))
    (make-application
     (make-letrec
      (list
       (make-let-binding
	var
	(make-lambda (map let-variable bindings) (named-let-body exp))))
      (list var))
     (map let-value bindings))))

(define (expand-let* exp)
  (if (null? (let*-bindings exp))
      (make-let (list (let*-body exp)))
      (let helper ((bindings (let*-bindings exp)))
	(if (null? bindings)
	    (make-begin (let*-body exp))
	    (make-let (list (car bindings)) (list (helper (cdr bindings))))))))

(define (expand-letrec exp)
  (let* ((bindings (letrec-bindings exp))
	 (temps (map (lambda (binding) (generate-variable))
		     (letrec-bindings exp))))
    (make-let
     (map (lambda (binding)
	    (make-let-binding (let-variable binding) unassigned))
	  bindings)
     (list
      (make-let
       (map (lambda (binding temp)
	      (make-let-binding temp (let-value binding)))
	    bindings temps)
       (append
	(map (lambda (binding temp)
	       (make-assignment (let-variable binding) temp))
	     bindings temps)
	(letrec-body exp)))))))

(define (expand-do exp)
  (let* ((loop-var (generate-variable))
	 (recursive-case-exp
	  (make-begin
	   (append
	    (do-iteration-sequence exp)
	    (list
	     (make-application loop-var (map do-step (do-clauses exp))))))))
    (make-named-let
     loop-var
     (map (lambda (clause)
	    (make-let-binding (do-variable clause) (do-initial clause)))
	  (do-clauses exp))
     (list
      (if (null? (do-result-sequence exp))
	  (make-if (make-application 'not (list (do-predicate exp)))
		   recursive-case-exp)
	  (make-if (do-predicate exp) (make-begin (do-result-sequence exp))
		   recursive-case-exp))))))

(define (expand-delay exp)
  (make-application
   'make-promise
   (list (make-lambda '() (list (delayed-expression exp))))))

(define generate-variable
  (let ((counter 0))
    (lambda ()
      (set! counter (+ counter 1))
      (string->symbol (string-append "Gg" (number->string counter))))))


;;; Primitives

(define (make-primitives)
  (define (argument k) (make-rt-vector-ref :argv k))
  (define (integer exp) (check-type "integer" (make-rt-integer? exp) exp))
  (define (character exp) (check-type "character" (make-rt-char? exp) exp))
  (define (pair exp) (check-type "pair" (make-rt-pair? exp) exp))
  (define (procedure exp) (check-type "procedure" (make-rt-procedure? exp) exp))
  (define (vector exp) (check-type "vector" (make-rt-vector? exp) exp))
  (define (check-type name predicate exp)
    (make-if-block
     (make-not predicate)
     (list
      (make-error-block
       (string-append (if (vowel? (string-ref name 0)) "Not an " "Not a ") name)
       exp))))
  (define (check-bounds i-exp j-exp k-exp)
    (make-if-block
     (make-or (make-> (make-* 3 i-exp) j-exp) (make-> j-exp (make-* 3 k-exp)))
     (list (make-error-block "Out of bounds" j-exp))))
  ;; This is certainly not ideal.
  (list
   (cons
    'eq?
    (make-primitive
     #f 2 #f
     (list
      (make-set-block
       "result" (make-rt-make-boolean (make-= (argument 0) (argument 1)))))))
   (cons
    'integer?
    (make-primitive
     #f 1 #f
     (list
      (make-set-block
       "result" (make-rt-make-boolean (make-rt-integer? (argument 0)))))))
   (cons
    '<
    (make-primitive
     #f 2 #f
     (list
      ;; (integer (argument 0))
      ;; (integer (argument 1))
      (make-set-block
       "result" (make-rt-make-boolean (make-rt-< (argument 0) (argument 1)))))))
   (cons
    '=
    (make-primitive
     #f 2 #f
     (list
      ;; (integer (argument 0))
      ;; (integer (argument 1))
      (make-set-block
       "result" (make-rt-make-boolean (make-rt-= (argument 0) (argument 1)))))))
   (cons
    '>
    (make-primitive
     #f 2 #f
     (list
      ;; (integer (argument 0))
      ;; (integer (argument 1))
      (make-set-block
       "result" (make-rt-make-boolean (make-rt-< (argument 1) (argument 0)))))))
   (cons
    '+
    (make-primitive
     #f 2 #f
     (list
      ;; (integer (argument 0))
      ;; (integer (argument 1))
      (make-set-block "result" (make-rt-+ (argument 0) (argument 1))))))
   (cons
    '*
    (make-primitive
     #f 2 #f
     (list
      ;; (integer (argument 0))
      ;; (integer (argument 0))
      (make-set-block "result" (make-rt-* (argument 0) (argument 1))))))
   (cons
    '-
    (make-primitive
     #f 2 #f
     (list
      ;; (integer (argument 0))
      ;; (integer (argument 1))
      (make-set-block "result" (make-rt-- (argument 0) (argument 1))))))
   (cons
    'quotient
    (make-primitive
     #f 2 #f
     (list
      ;; (integer (argument 0))
      ;; (integer (argument 1))
      (make-set-block
       "result" (make-/ (make-rt-integer->scratch-integer (argument 0))
			(make-rt-integer->scratch-integer (argument 1))))
      (make-if-else-block
       (make-> :result 0)
       (list (make-set-block "result" (make-monad-block "floor" :result)))
       (list (make-set-block "result" (make-monad-block "ceiling" :result))))
      (make-set-block
       "result" (make-scratch-integer->rt-integer :result)))))
   (cons
    'modulo
    (make-primitive
     #f 2 #f
     (list
      ;; (integer (argument 0))
      ;; (integer (argument 1))
      (make-set-block
       "result"
       (make-scratch-integer->rt-integer
	(make-mod-block (make-rt-integer->scratch-integer (argument 0))
			(make-rt-integer->scratch-integer (argument 1))))))))
   (cons
    'pair?
    (make-primitive
     #f 1 #f
     (list
      (make-set-block "result"
		      (make-rt-make-boolean (make-rt-pair? (argument 0)))))))
   (cons
    'cons
    (make-primitive
     #f 2 #f
     (list (make-cons-block (argument 0) (argument 1)))))
   (cons
    'car
    (make-primitive
     #f 1 #f (list ;; (pair (argument 0))
	      (make-set-block "result" (make-rt-car (argument 0))))))
   (cons
    'cdr
    (make-primitive
     #f 1 #f (list ;; (pair (argument 0))
	      (make-set-block "result" (make-rt-cdr (argument 0))))))
   (cons
    'set-car!
    (make-primitive
     #f 2 #f (list ;; (pair (argument 0))
	      (make-rt-set-car! (argument 0) (argument 1)))))
   (cons
    'set-cdr!
    (make-primitive
     #f 2 #f (list ;; (pair (argument 0))
	      (make-rt-set-cdr! (argument 0) (argument 1)))))
   (cons
    'symbol?
    (make-primitive
     #f 1 #f
     (list
      (make-set-block
       "result" (make-rt-make-boolean (make-rt-symbol? (argument 0)))))))
   (cons
    'char?
    (make-primitive
     #f 1 #f
     (list
      (make-set-block
       "result" (make-rt-make-boolean (make-rt-char? (argument 0)))))))
   (cons
    'char-ci=?
    (make-primitive
     #f 2 #f
     (list
      (character (argument 0))
      (character (argument 1))
      (make-set-block
       "result"
       (make-rt-make-boolean (make-rt-char-ci=? (argument 0) (argument 1)))))))
   (cons
    'char-ci<?
    (make-primitive
     #f 2 #f
     (list
      (character (argument 0))
      (character (argument 1))
      (make-set-block
       "result"
       (make-rt-make-boolean (make-rt-char-ci<? (argument 0) (argument 1)))))))
   (cons
    'char-ci>?
    (make-primitive
     #f 2 #f
     (list
      (character (argument 0))
      (character (argument 1))
      (make-set-block
       "result"
       (make-rt-make-boolean (make-rt-char-ci<? (argument 1) (argument 0)))))))
   (cons
    'char-upper-case?
    (make-primitive
     #f 1 #f
     (list
      (character (argument 0))
      (make-switch-costume-block "costume1")
      (make-switch-costume-block (argument 0))
      (make-set-block
       "result"
       (make-rt-make-boolean
	(make-not (make-= (make-costume-number-block) 1)))))))
   (cons
    'vector?
    (make-primitive
     #f 1 #f
     (list
      (make-set-block "result"
		      (make-rt-make-boolean (make-rt-vector? (argument 0)))))))
   (cons
    'make-vector
    (make-primitive
     #f 1 #f
     (list (integer (argument 0))
	   (make-make-vector-block (make-/ (argument 0) 3)))))
   (cons
    'vector
    (make-primitive
     #t 1 #f (list (make-set-block "result" :argv))))
   (cons
    'vector-length
    (make-primitive
     #f 1 #f
     (list (vector (argument 0))
	   (make-set-block "result"
			   (make-scratch-integer->rt-integer
			    (make-rt-vector-length (argument 0)))))))
   (cons
    'vector-ref
    (make-primitive
     #f 2 #f
     (list
      (vector (argument 0)) (integer (argument 1))
      (check-bounds 0 (argument 1) (make-rt-vector-length (argument 0)))
      (make-set-block
       "result"
       (make-rt-vector-ref
	(argument 0) (make-rt-integer->scratch-integer (argument 1)))))))
   (cons
    'vector-set!
    (make-primitive
     #f 3 #f
     (list
      (vector (argument 0)) (integer (argument 1))
      (check-bounds 0 (argument 1) (make-rt-vector-length (argument 0)))
      (make-rt-vector-set! (argument 0)
			   (make-rt-integer->scratch-integer (argument 1))
			   (argument 2)))))
   (cons
    'vector->list
    (make-primitive
     #f 1 #f
     (list
      (vector (argument 0))
      (make-vector->list-from-block (argument 0) 0))))
   (cons
    'procedure?
    (make-primitive
     #f 1 #f
     (list
      (make-set-block
       "result" (make-rt-make-boolean (make-rt-procedure? (argument 0)))))))
   (cons
    'apply
    (make-primitive
     #t 2 #t
     (list
      (make-set-block "proc" (argument 0))
      ;; (procedure :proc)
      (make-list->vector-leaving-block
       (argument (make-- (make-rt-vector-length :argv) 1))
       (make-- (make-rt-vector-length :argv) 2))
      (make-rt-copy-elements (make-- (make-rt-vector-length :argv) 2) :argv 1
			     :result 0)
      (make-set-block "argv" :result)
      (make-apply-block :proc))))
   (cons
    'call-with-current-continuation
    (make-primitive
     #f 1 #t
     (list
      (make-save-stack-block)
      (make-make-escape-procedure-block :continue :result)
      (make-set-block "proc" :result)
      (make-make-vector-block 1)
      (make-rt-vector-set! :result 0 :proc)
      (make-set-block "proc" (argument 0))
      (procedure :proc)
      (make-set-block "argv" :result)
      (make-apply-block :proc))))))

(define (vowel? char) (memq char '(#\a #\e #\i #\o #\u)))


;;; Code generation

(define (compile-with-labels exp env tail?)
  (cond ((self-evaluating? exp) (compile-datum exp))
	((identifier? exp) (compile-variable-reference exp env))
	((application-or-special-form? exp)
	 (if (identifier? (operator-or-keyword exp))
	     (let ((thing (lookup (operator-or-keyword exp) env)))
	       (if (special-form? thing)
		   ((special-form-compiler thing) exp env tail?)
		   (compile-application exp env tail?)))
	     (compile-application exp env tail?)))
	(else (error "Unknown expression type" exp))))

(define (compile-datum obj)
  (cond ((null? obj)
	 (list (make-set-block "result" the-empty-lists-representation)))
	((boolean? obj)
	 (list
	  (make-set-block "result"
			  (if obj trues-representation falses-representation))))
	((eq? obj unassigned)
	 (list (make-set-block "result" unassigneds-representation)))
	((integer? obj)
	 (list (make-set-block "result" (integers-representation obj))))
	((symbol? obj)
	 (list (make-set-block "result" (symbols-representation obj))))
	((char? obj)
	 (list (make-set-block "result" (characters-representation obj))))
	(else (error "Unknown datum type" obj))))

(define (compile-variable-reference exp env)
  (let ((thing (lookup exp env)))
    (cond ((special-form? thing) (error "Loose keyword" exp))
	  ((primitive? thing)
	   (if (primitive-pc thing)
	       (list
		(make-make-procedure-block
		 the-empty-lists-representation
		 (primitive-min-arity thing)
		 (if (primitive-variadic? thing) (make-not #f) #f)
		 (primitive-pc thing)))
	       (let ((proc (make-label))
		     (after-proc (make-label)))
		 (set-primitive-pc! thing proc)
		 (append
		  (list (make-set-block "pc" after-proc)
			proc)
		  (primitive-code thing)
		  (list
		   ;; May not be necessary.
		   (make-set-block "pc" :continue)
		   after-proc
		   (make-make-procedure-block
		    the-empty-lists-representation
		    (primitive-min-arity thing)
		    (if (primitive-variadic? thing) (make-not #f) #f)
		    proc))))))
	  (else
	   (let loop ((env-exp :env)
		      (i (frame thing)))
	     (if (zero? i)
		 (list
		  (make-set-block "result"
				  (make-rt-vector-ref (make-rt-car env-exp)
						      (offset thing))))
		 (loop (make-rt-cdr env-exp) (- i 1))))))))

(define (compile-lambda exp env tail?)
  (define (analyze-parameters params)
    (cond ((null? params) (values 0 #f))
	  ((symbol? params) (values 0 #t))
	  (else
	   (call-with-values
	    (lambda () (analyze-parameters (cdr params)))
	    (lambda (min-arity variadic?)
	      (values (+ min-arity 1) variadic?))))))
  (let ((proc (make-label))
	(after-proc (make-label)))
    (call-with-values
     (lambda () (analyze-parameters (lambda-parameters exp)))
     (lambda (min-arity variadic?)
       (append
	(list (make-set-block "pc" after-proc)
	      proc)
	(if variadic?
	    (list (make-make-vector-block (+ min-arity 1))
		  (make-set-block "frame" :result)
		  (make-rt-copy-elements min-arity :argv 0 :frame 0)
		  (make-vector->list-from-block :argv min-arity)
		  (make-rt-vector-set! :frame min-arity :result)
		  (make-cons-block :frame :env)
		  (make-set-block "env" :result))
	    (list (make-cons-block :argv :env)
		  (make-set-block "env" :result)))
	(compile-sequence (scan-out-definitions (lambda-body exp))
			  (extend-with-variables (lambda-parameters exp) env)
			  #t)
	(list
	 ;; This is unnecessary if the tail expression is a non-open-coded
	 ;; procedure call (and may not be necessary even if it is open-coded.)
	 (make-set-block "pc" :continue)
	 after-proc
	 (make-make-procedure-block :env min-arity
				    (if variadic? (make-not #f) #f) proc)))))))

(define (compile-if exp env tail?)
  (append
   (save-state)
   (compile-with-labels (if-predicate exp) env #f)
   (restore-state)
   (if (if-has-alternative? exp)
       (let ((alternative (make-label))
	     (end (make-label)))
	 (append
	  (list (make-if-block (make-= :result falses-representation)
			       (list (make-set-block "pc" alternative))))
	  (compile-with-labels (if-consequent exp) env tail?)
	  (list (make-set-block "pc" end)	; This may be dead code.
		alternative)
	  (compile-with-labels (if-alternative exp) env tail?)
	  (list end)))
       (let ((end (make-label)))
	 (append
	  (list (make-if-block (make-= :result falses-representation)
			       (list (make-set-block "pc" end))))
	  (compile-with-labels (if-consequent exp) env tail?)
	  (list end))))))

(define (compile-let exp env tail?)
  (if (named-let? exp)
      (compile-with-labels (expand-named-let exp) env tail?)
      (append
       (compile-arguments (map let-value (let-bindings exp)) env)
       (list (make-cons-block :argv :env)
	     (make-set-block "env" :result))
       (compile-sequence
	(scan-out-definitions (let-body exp))
	(extend-with-variables (map let-variable (let-bindings exp)) env)
	tail?))))

(define (compile-assignment exp env tail?)
  (let ((loc (lookup (assignment-variable exp) env)))
    (append
     (if (or (self-evaluating? (assignment-value exp))
	     (quotation? (assignment-value exp))
	     (lambda? (assignment-value exp))
	     (identifier? (assignment-value exp)))
	 '()
	 (save-state))
     (compile-with-labels (assignment-value exp) env #f)
     (if (or (self-evaluating? (assignment-value exp))
	     (quotation? (assignment-value exp))
	     (lambda? (assignment-value exp))
	     (identifier? (assignment-value exp)))
	 '()
	 (restore-state))
     (let loop ((env-exp :env)
		(i (frame loc)))
       (if (zero? i)
	   (list (make-rt-vector-set! (make-rt-car env-exp) (offset loc)
				      :result))
	   (loop (make-rt-cdr env-exp) (- i 1)))))))

(define (compile-application exp env tail?)
  (define (compile-application-without-open-coding)
    (append
     (compile-arguments (operands exp) env)
     (if (or (identifier? (operator exp)) (lambda? (operator exp)))
	 '()
	 (save-state))
     (compile-with-labels (operator exp) env #f)
     (if (or (identifier? (operator exp)) (lambda? (operator exp)))
	 '()
	 (restore-state))
     (if tail?
	 (list (make-apply-block :result))
	 (let ((after-call (make-label)))
	   (list (make-set-block "continue" after-call)
		 (make-apply-block :result)
		 after-call)))))
  (if (symbol? (operator exp))
      (let ((loc (lookup (operator exp) env)))
	(if (primitive? loc)
	    (let ((min-arity (primitive-min-arity loc))
		  (k (length (operands exp))))
	      (cond ((< k min-arity)
		     (error "Too few arguments" exp))
		    ((and (> k min-arity) (not (primitive-variadic? loc)))
		     (error "Too many arguments" exp))
		    (else
		     (if (or tail? (not (primitive-makes-tail-call? loc)))
			 (append
			  (compile-arguments (operands exp) env)
			  (primitive-code loc))
			 (let ((after-call (make-label)))
			   (append
			    (compile-arguments (operands exp) env)
			    (list (make-set-block "continue" after-call))
			    (primitive-code loc)
			    (list after-call)))))))
	    (compile-application-without-open-coding)))
      (compile-application-without-open-coding)))

(define (compile-arguments args env)
  (let loop ((k 0)
	     (results '())
	     (args args))
    (cond ((null? args)
	   (apply append
		  (list (make-make-vector-block k)
			(make-set-block "argv" :result))
		  (reverse results)))
	  ((or (self-evaluating? (car args)) (quotation? (car args))
	       (lambda? (car args)) (identifier? (car args)))
	   (loop (+ k 1)
		 (cons
		  (append
		   (compile-with-labels (car args) env #f)
		   (list (make-rt-vector-set! :argv k :result)))
		  results)
		 (cdr args)))
	  (else
	   (loop (+ k 1)
		 (cons
		  (append
		   (save-state)
		   (compile-with-labels (car args) env #f)
		   (restore-state)
		   (list (make-rt-vector-set! :argv k :result)))
		  results)
		 (cdr args))))))

(define (compile-sequence seq env tail?)
  (if (null? (cdr seq))
      (compile-with-labels (car seq) env tail?)
      (append
       (save-state)
       (compile-with-labels (car seq) env #f)
       (restore-state)
       (compile-sequence (cdr seq) env tail?))))

(define (save-state)
  ;; Saving all of these is unnecessary.
  (list (make-add-block :env "stack")
	(make-add-block :argv "stack")
	(make-add-block (make-* 3 :continue) "stack")))

(define (restore-state)
  (list (make-set-block "continue" (make-/ (make-item-block "last" "stack") 3))
	(make-delete-block "last" "stack")
	(make-set-block "argv" (make-item-block "last" "stack"))
	(make-delete-block "last" "stack")
	(make-set-block "env" (make-item-block "last" "stack"))
	(make-delete-block "last" "stack")))

(define (intermediate->basic-blocks instructions)
  (define (split-at-labels-and-jumps instructions)
    (define (jump? block)
      (or (and (set-block? block)
	       (string=? (set-block-variable block) "pc"))
	  (apply-block? block)))
    (define (branch? block)
      (and (if-block? block)
	   (let ((block (car (if-block-consequent block))))
	     (and (set-block? block)
		  (string=? (set-block-variable block) "pc")))))
    (let ((label-pcs (make-vector *label-counter*)))
      (let loop ((i 0)
		 (size 128)
		 (result (make-vector 128))
		 (accum '())
		 (instructions instructions))
	(cond ((null? instructions)
	       (cond ((null? accum)
		      (values (shrink-vector result i) label-pcs))
		     ((= i size)
		      (let ((result (grow-vector result (+ i 1))))
			(vector-set! result i (reverse accum))
			(values result label-pcs)))
		     ((= (+ i 1) size)
		      (vector-set! result i (reverse accum))
		      (values result label-pcs))
		     (else
		      (vector-set! result i (reverse accum))
		      (values (shrink-vector result (+ i 1)) label-pcs))))
	      ((= i size)
	       (loop i (* 2 size) (grow-vector result (* 2 size))
		     accum instructions))
	      ((and (not (null? accum))
		    (not (label? (car instructions)))
		    (or (jump? (car instructions))
			(branch? (car instructions))))
	       (vector-set! result i
			    (reverse (cons (car instructions) accum)))
	       (loop (+ i 1) size result '() (cdr instructions)))
	      ((label? (car instructions))
	       (if (null? accum)
		   (begin
		     (vector-set! label-pcs (label-count (car instructions)) i)
		     (loop i size result accum (cdr instructions)))
		   (begin
		     (vector-set! label-pcs (label-count (car instructions))
				  (+ i 1))
		     (vector-set! result i (reverse accum))
		     (loop (+ i 1) size result '() (cdr instructions)))))
	      (else
	       (loop i size result (cons (car instructions) accum)
		     (cdr instructions)))))))
  (define (substitute-labels! basic-blocks label-pcs)
    (define (substitute-labels exp)
      (cond ((label? exp) (vector-ref label-pcs (label-count exp)))
	    ((pair? exp)
	     (cons (substitute-labels (car exp))
		   (substitute-labels (cdr exp))))
	    (else exp)))
    (do ((i 0 (+ i 1)))
	((= i (vector-length basic-blocks)))
      (let ((basic-block (vector-ref basic-blocks i)))
	(vector-set! basic-blocks i (substitute-labels basic-block)))))
  (call-with-values
   (lambda () (split-at-labels-and-jumps instructions))
   (lambda (basic-blocks label-pcs)
     (substitute-labels! basic-blocks label-pcs)
     basic-blocks)))

(define (generate-script scratch k)
  (list (make-set-block "continue" k)
	(make-until-block (make-> :pc k)
			  (append scratch (list (make-change-block "pc" 1))))
	(make-external-representation-block :result)
	(make-think-block :result)))

(define (basic-blocks->scratch basic-blocks i j)
  (if (= i j)
      (vector-ref basic-blocks (- i 1))
      (list
       (make-if-else-block
	(make-< :pc (quotient (+ i j 1) 2))
	(basic-blocks->scratch basic-blocks i (quotient (- (+ i j) 1) 2))
	(basic-blocks->scratch basic-blocks (quotient (+ i j 1) 2) j)))))


;;; Syntax

(define unassigned (list '*unassigned*))

(define (definition? form) (tagged-list? form 'define))
(define (definition-variable definition)
  (if (symbol? (cadr definition))
      (cadr definition)
      (caadr definition)))
(define (definition-value definition)
  (if (symbol? (cadr definition))
      (caddr definition)
      (make-lambda (cdadr definition) (cddr definition))))

(define (self-evaluating? exp)
  (or (number? exp) (char? exp) (boolean? exp) (eq? exp unassigned)))

(define (identifier? exp) (symbol? exp))
(define (identifier<? id1 id2)
  (string<? (symbol->string id1) (symbol->string id2)))

(define (application-or-special-form? exp) (pair? exp))
(define (operator-or-keyword exp) (car exp))
(define (make-application proc args) (cons proc args))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (quotation? exp) (tagged-list? exp 'quote))
(define (quoted-datum exp) (cadr exp))

(define (make-lambda params body) (cons 'lambda (cons params body)))
(define (lambda? exp) (tagged-list? exp 'lambda))
(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-if predicate consequent . alternatives)
  (cons 'if (cons predicate (cons consequent alternatives))))
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp) (cadddr exp))
(define (if-has-alternative? exp) (not (null? (cdddr exp))))

(define (cond-clauses exp) (cdr exp))
(define (cond-else? clause) (eq? (car clause) 'else))
(define (cond-procedure? clause)
  (and (not (null? (cdr clause))) (eq? (cadr clause) '=>)))
(define (cond-predicate clause) (car clause))
(define (cond-body clause) (cdr clause))
(define (cond-recipient clause) (caddr clause))

(define (and-tests exp) (cdr exp))

(define (or-tests exp) (cdr exp))

(define (make-let bindings body) (cons 'let (cons bindings body)))
(define (let-bindings exp) (cadr exp))
(define (let-body exp) (cddr exp))
(define (make-let-binding var val) (list var val))
(define (let-variable binding) (car binding))
(define (let-value binding) (cadr binding))

(define (make-named-let var bindings body)
  (cons 'let (cons var (cons bindings body))))
(define (named-let? exp) (and (tagged-list? exp 'let) (symbol? (cadr exp))))
(define (named-let-variable exp) (cadr exp))
(define (named-let-bindings exp) (caddr exp))
(define (named-let-body exp) (cdddr exp))

(define (let*-bindings exp) (cadr exp))
(define (let*-body exp) (cddr exp))

(define (make-letrec bindings body) (cons 'letrec (cons bindings body)))
(define (letrec-bindings exp) (cadr exp))
(define (letrec-body exp) (cddr exp))

(define (make-begin actions) (cons 'begin actions))
(define (begin-actions exp) (cdr exp))

(define (make-assignment var val) (list 'set! var val))
(define (assignment-variable exp) (cadr exp))
(define (assignment-value exp) (caddr exp))

(define (do-clauses exp) (cadr exp))
(define (do-predicate exp) (caaddr exp))
(define (do-result-sequence exp) (cdaddr exp))
(define (do-iteration-sequence exp) (cdddr exp))
(define (do-variable clause) (car clause))
(define (do-initial clause) (cadr clause))
(define (do-step clause)
  (if (null? (cddr clause))
      (car clause)
      (caddr clause)))

(define (delayed-expression exp) (cadr exp))

(define (tagged-list? obj tag) (and (pair? obj) (eq? (car obj) tag)))


;;; Compile time environment

(define the-empty-environment '())
(define (extend-with-variables vars env) (cons vars env))
(define (extend-with-special-forms-and-primitives bindings env)
  (let ((vec (list->vector bindings)))
    (sort-vector! (lambda (b1 b2) (identifier<? (car b1) (car b2))) vec)
    (cons vec env)))
(define (lookup id env)
  (let loop ((env env)
	     (i 0))
    (cond ((eq? env the-empty-environment) (error "Unbound variable" id))
	  ((vector? (car env))
	   (let ((b (vector-binary-search identifier<? car (car env) id)))
	     (if b (cdr b) (loop (cdr env) i))))
	  (else
	   (let scan ((vars (car env))
		      (j 0))
	     (cond ((pair? vars)
		    (if (eq? (car vars) id)
			(make-location i j)
			(scan (cdr vars) (+ j 1))))
		   ((eq? vars id) (make-location i j))
		   (else (loop (cdr env) (+ i 1)))))))))
(define (bound? id env)
  (cond ((eq? env the-empty-environment) #f)
	((vector? (car env))
	 (or (vector-binary-search identifier<? car (car env) id)
	     (bound? id (cdr env))))
	(else (or (memq id (car env)) (bound? id (cdr env))))))

(define (make-special-form compiler) (cons 'special-form compiler))
(define (special-form? obj) (tagged-list? obj 'special-form))
(define (special-form-compiler obj) (cdr obj))

(define (make-primitive var? min-arity tail-call? code)
  (vector 'primitive var? min-arity tail-call? code #f))
(define (primitive? obj)
  (and (vector? obj)
       (> (vector-length obj) 0)
       (eq? (vector-ref obj 0) 'primitive)))
(define (primitive-variadic? primitive) (vector-ref primitive 1))
(define (primitive-min-arity primitive) (vector-ref primitive 2))
(define (primitive-makes-tail-call? primitive) (vector-ref primitive 3))
(define (primitive-code primitive) (vector-ref primitive 4))
(define (primitive-pc primitive) (vector-ref primitive 5))
(define (set-primitive-pc! primitive pc) (vector-set! primitive 5 pc))

(define (make-location i j) (cons i j))
(define (frame loc) (car loc))
(define (offset loc) (cdr loc))


(define (flatmap proc lst) (apply append (map proc lst)))

;;; Vectors

(define (vector-binary-search rel sel vec key)
  (let loop ((i 0)
	     (j (- (vector-length vec) 1)))
    (if (> i j)
	#f
	(let* ((k (quotient (+ i j) 2))
	       (obj (vector-ref vec k)))
	  (cond ((rel key (sel obj)) (loop i (- k 1)))
		((rel (sel obj) key) (loop (+ k 1) j))
		(else obj))))))

(define (sort-vector! rel vec)
  ;; Insertion sort
  (if (> (vector-length vec) 1)
      (do ((i 1 (+ i 1)))
	  ((= i (vector-length vec)))
	(do ((j (- i 1) (- j 1)))
	    ((not (and (>= j 0)
		       (rel (vector-ref vec (+ j 1)) (vector-ref vec j)))))
	  (vector-swap! vec (+ j 1) j)))))

(define (vector-swap! vec i j)
  (let ((obj (vector-ref vec i)))
    (vector-set! vec i (vector-ref vec j))
    (vector-set! vec j obj)))

(define (grow-vector vec k)
  (let ((result (make-vector k)))
    (do ((i 0 (+ i 1)))
	((= i (vector-length vec)) result)
      (vector-set! result i (vector-ref vec i)))))

(define (shrink-vector vec k)
  (let ((result (make-vector k)))
    (do ((i 0 (+ i 1)))
	((= i k) result)
      (vector-set! result i (vector-ref vec i)))))


;;; Intermediate representation

(define *label-counter* 0)
(define (make-label)
  (let ((n *label-counter*))
    (set! *label-counter* (+ *label-counter* 1))
    (list 'label n)))
(define (label? obj) (tagged-list? obj 'label))
(define (label-count label) (cadr label))


;;; Runtime environment

(define (make-vector->list-from-block vec j)
  (make-custom-block-call "make a list with items from vector %n from %n"
			  vec j))
(define (make-list->vector-leaving-block lst i)
  (make-custom-block-call "make a vector with items from list %n leaving %n"
			  lst i))
(define (make-save-stack-block) (make-custom-block-call "save stack"))
(define (make-cons-block obj1 obj2)
  (make-custom-block-call "cons %s %s" obj1 obj2))
(define (make-make-procedure-block env min-arity variadic? pc)
  (make-custom-block-call "make a procedure %n %n %b %n"
			  env min-arity variadic? pc))
(define (make-make-escape-procedure-block pc stack)
  (make-custom-block-call "make an escape procedure %n %n" pc stack))
(define (make-make-vector-block length)
  (make-custom-block-call "make a vector %n" length))
(define (make-apply-block proc)
  (make-custom-block-call "apply %n" proc))
(define (make-error-block message obj)
  (make-custom-block-call "error %s %s" message obj))
(define (make-external-representation-block obj)
  (make-custom-block-call "external representation of %s" obj))

(define (apply-block? block)
  (and (custom-block-call? block)
       (string=? (custom-block-name block) "apply %n")))

(define (make-rt-integer? obj) (make-= (make-mod-block obj 3) 0))
(define (make-scratch-integer->rt-integer n) (make-* 3 n))
(define (make-rt-+ m n) (make-+ m n))
(define (make-rt-- m n) (make-- m n))
(define (make-rt-* m n) (make-* (make-/ m 3) n))
(define (make-rt-< m n) (make-< m n))
(define (make-rt-= m n) (make-= m n))
(define (make-rt-integer->scratch-integer n) (make-/ n 3))
(define (make-rt-make-boolean n) (make-- (make-* 3 n) 8))
(define (make-rt-pair? obj)
  (make-and (make-= (make-mod-block obj 3) 1)
	    (make-= (make-item-block obj "heap") -1)))
(define (make-rt-car pair) (make-item-block (make-+ pair 1) "heap"))
(define (make-rt-cdr pair) (make-item-block (make-+ pair 2) "heap"))
(define (make-rt-set-car! pair obj)
  (make-replace-block (make-+ pair 1) "heap" obj))
(define (make-rt-set-cdr! pair obj)
  (make-replace-block (make-+ pair 2) "heap" obj))
(define (make-rt-symbol? obj)
  (make-not (make-or (make-= (make-+ obj 0) obj)
		     (make-= (make-letter-block 1 obj) #\#))))
(define (make-rt-char? obj) (make-= (make-letter-block 1 exp) "#"))
(define (make-rt-char-ci<? char1 char2) (make-< char1 char2))
(define (make-rt-char-ci=? char1 char2) (make-= char1 char2))
(define (make-rt-procedure? obj)
  (make-and (make-= (make-mod-block obj 3) 1)
	    (make-or
	     (make-= (make-item-block obj "heap") -2)
	     (make-= (make-item-block obj "heap") -3))))
(define (make-rt-vector? obj)
  (make-and (make-> obj 0) (make-= (make-mod-block obj 3) 2)))
(define (make-rt-vector-length vec) (make-item-block (make-- vec 1) "heap"))
(define (make-rt-vector-ref vec k) (make-item-block (make-+ vec k) "heap"))
(define (make-rt-vector-set! vec k obj)
  (make-replace-block (make-+ vec k) "heap" obj))
(define (make-rt-copy-elements k vec1 i vec2 j)
  (make-custom-block-call "copy %n objects from address %n to %n"
			  k (make-+ vec1 i) (make-+ vec2 j)))

(define the-empty-lists-representation -2)
(define trues-representation -5)
(define falses-representation -8)
(define unassigneds-representation -11)
(define (integers-representation n) (* 3 n))
(define (symbols-representation sym) (symbol->string sym))
(define (characters-representation char) (string #\# #\\ char))


;;; Scratch

(define (make-think-block thought) (make-block "think:" thought))
(define (make-switch-costume-block name) (make-block "lookLike:" name))
(define (make-costume-number-block) (make-block "costumeIndex"))
(define (make-if-block predicate consequent)
  (make-block "doIf" predicate consequent))
(define (make-if-else-block predicate consequent alternative)
  (make-block "doIfElse" predicate consequent alternative))
(define (make-until-block predicate body) (make-block "doUntil" predicate body))
(define (make-+ x y) (if (and (number? y) (= y 0)) x (make-block "+" x y)))
(define (make-- x y) (make-block "-" x y))
(define (make-* x y) (make-block "*" x y))
(define (make-/ x y) (make-block "/" x y))
(define (make-< x y) (make-block "<" x y))
(define (make-= x y) (make-block "=" x y))
(define (make-> x y) (make-block ">" x y))
(define (make-mod-block a b) (make-block "%" a b))
(define (make-monad-block f x) (make-block "computeFunction:of:" f x))
(define (make-and a b) (make-block "&" a b))
(define (make-or a b) (make-block "|" a b))
(define (make-not a) (make-block "not" a))
(define (make-letter-block k string) (make-block "letter:of:" k string))
(define (make-variable-block var) (make-block "readVariable" var))
(define (make-set-block var val) (make-block "setVar:to:" var val))
(define (make-change-block var val) (make-block "changeVar:by:" var val))
(define (make-item-block k lst) (make-block "getLine:ofList:" k lst))
(define (make-add-block obj lst) (make-block "append:toList:" obj lst))
(define (make-delete-block k lst) (make-block "deleteLine:ofList:" k lst))
(define (make-replace-block k obj lst)
  (make-block "setLine:ofList:to:" k obj lst))
(define (make-custom-block-call spec . args)
  (apply make-block "call" spec args))

(define (if-block? block) (string=? (block-selector block) "doIf"))
(define (if-block-consequent block) (cadr (block-arguments block)))
(define (set-block? block)
  (string=? (block-selector block) "setVar:to:"))
(define (set-block-variable block) (car (block-arguments block)))
(define (custom-block-call? block) (string=? (block-selector block) "call"))
(define (custom-block-name block) (car (block-arguments block)))

(define (make-block selector . args) (cons selector args))
(define (block-selector block) (car block))
(define (block-arguments block) (cdr block))

(define :result (make-variable-block "result"))
(define :tospace (make-variable-block "tospace"))
(define :free (make-variable-block "free"))
(define :env (make-variable-block "env"))
(define :frame (make-variable-block "frame"))
(define :argv (make-variable-block "argv"))
(define :pc (make-variable-block "pc"))
(define :continue (make-variable-block "continue"))
(define :proc (make-variable-block "proc"))

;;; JSON output

(define (display-json obj port)
  (cond ((number? obj) (write obj port))
	((eq? obj #f) (display "false" port))
	((null? obj) (display "[]" port))
	((pair? obj)
	 (write-char #\[ port)
	 (do ((lst obj (cdr lst)))
	     ((null? (cdr lst))
	      (display-json (car lst) port))
	   (display-json (car lst) port)
	   (write-char #\, port))
	 (write-char #\] port))
	((string? obj)
	 (write-char #\" port)
	 (do ((i 0 (+ i 1)))
	     ((= i (string-length obj)))
	   (let ((char (string-ref obj i)))
	     (if (or (char=? char #\")
		     (char=? char #\\))
		 (write-char #\\ port))
	     (write-char char port)))
	 (write-char #\" port))))
