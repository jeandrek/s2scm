;;; 6.1 Equivalence predicates

(define eq?
  (let ((old-eq? eq?))
    (lambda (obj1 obj2)
      (if (and (char? obj1) (char? obj2))
	  (char=? obj1 obj2)
	  (old-eq? obj1 obj2)))))

(define (eqv? obj1 obj2)
  (if (and (number? obj1) (number? obj2)
	   (or (and (exact? obj1) (exact? obj2))
	       (and (inexact? obj1) (inexact? obj2))))
      (= obj1 obj2)
      (eq? obj1 obj2)))

(define (equal? obj1 obj2)
  (cond ((and (pair? obj1) (pair? obj2))
	 (and (equal? (car obj1) (car obj2)) (equal? (cdr obj1) (cdr obj2))))
	((and (vector? obj1) (vector? obj2))
	 (let ((k (vector-length obj1)))
	   (if (= k (vector-length obj2))
	       (let loop ((i 0))
		 (cond ((= i k) #t)
		       ((equal? (vector-ref obj1 i) (vector-ref obj2 i))
			(loop (+ i 1)))
		       (else #f)))
	       #f)))
	(else (eqv? obj1 obj2))))


;;; 6.2.5 Numerical operations

(define (number? obj) (integer? obj))

(define (exact? n) #t)
(define (inexact? n) #f)

(define =
  (let ((integer-= =))
    (define (dyadic-= z1 z2)
      (cond ((and (integer? z1) (integer? z2)) (integer-= z1 z2))
	    ))
    (lambda (z1 z2 . zs)
      (cond ((null? zs) (dyadic-= z1 z2))
	    ((dyadic-= z1 z2) (apply = z2 zs))
	    (else #f)))))
(define <=
  (let ((dyadic-> >))
    (lambda (x1 x2 . xs)
      (cond ((null? xs) (not (dyadic-> x1 x2)))
	    ((dyadic-> x1 x2) #f)
	    (else (apply <= x2 xs))))))
(define >=
  (let ((dyadic-< <))
    (lambda (x1 x2 . xs)
      (cond ((null? xs) (not (dyadic-< x1 x2)))
	    ((dyadic-< x1 x2) #f)
	    (else (apply >= x2 xs))))))
(define <
  (let ((dyadic-< <))
    (lambda (x1 x2 . xs)
      (cond ((null? xs) (dyadic-< x1 x2))
	    ((dyadic-< x1 x2) (apply < x2 xs))
	    (else #f)))))
(define >
  (let ((dyadic-> >))
    (lambda (x1 x2 . xs)
      (cond ((null? xs) (dyadic-> x1 x2))
	    ((dyadic-> x1 x2) (apply > x2 xs))
	    (else #f)))))

(define (zero? z) (= z 0))
;; (define (positive? x) (> x 0))
;; (define (negative? x) (< x 0))
;; (define (odd? n) (zero? (modulo n 2)))
;; (define (even? n) (zero? (modulo n 2)))

;; (define (max x . xs) (fold-left (lambda (y x) (if (> x y) x y)) x xs))
;; (define (min x . xs) (fold-left (lambda (y x) (if (< x y) x y)) x xs))

(define +
  (let ((dyadic-+ +))
    (lambda zs (fold-left dyadic-+ 0 zs))))

(define -
  (let ((dyadic-- -))
    (lambda (z . zs)
      (if (null? zs)
	  (dyadic-- 0 z)
	  (fold-left dyadic-- z zs)))))

(define *
  (let ((dyadic-* *))
    (lambda zs (fold-left dyadic-* 1 zs))))

;; (define (abs x) (if (negative? x) (- x) x))

;; (define (remainder m n) (- m (* n (quotient m n))))

;; (define (gcd . ns)
;;   (define (gcd-2 a b)
;;     (if (zero? b)
;; 	a
;; 	(gcd-2 b (remainder a b))))
;;   (fold-left gcd-2 0 ns))

;; (define (lcm . ns)
;;   (if (null? ns)
;;       1
;;       (quotient (apply * ns) (apply gcd ns))))

;; (define (expt b n)
;;   (let loop ((a 1)
;; 	     (b b)
;; 	     (n n))
;;     (cond ((zero? n) a)
;; 	  ((even? n)
;; 	   (loop a (* b b) (quotient n 2)))
;; 	  (else
;; 	   (loop (* a b) b (- n 1))))))


;;; 6.3.1 Booleans

(define (not obj) (if obj #f #t))

;; (define (boolean? obj) (or (eq? obj #t) (eq? obj #f)))


;;; 6.3.2 Pairs and lists

;; (define (caar pair) (car (car pair)))
;; (define (cadr pair) (car (cdr pair)))
;; (define (cdar pair) (cdr (car pair)))
;; (define (cddr pair) (cdr (cdr pair)))
;; (define (caaar pair) (car (car (car pair))))
;; (define (caadr pair) (car (car (cdr pair))))
;; (define (cadar pair) (car (cdr (car pair))))
;; (define (caddr pair) (car (cdr (cdr pair))))
;; (define (cdaar pair) (cdr (car (car pair))))
;; (define (cdadr pair) (cdr (car (cdr pair))))
;; (define (cddar pair) (cdr (cdr (car pair))))
;; (define (cdddr pair) (cdr (cdr (cdr pair))))
;; (define (caaaar pair) (car (car (car (car pair)))))
;; (define (caaadr pair) (car (car (car (cdr pair)))))
;; (define (caadar pair) (car (car (cdr (car pair)))))
;; (define (caaddr pair) (car (car (cdr (cdr pair)))))
;; (define (cadaar pair) (car (cdr (car (car pair)))))
;; (define (cadadr pair) (car (cdr (car (cdr pair)))))
;; (define (caddar pair) (car (cdr (cdr (car pair)))))
;; (define (cadddr pair) (car (cdr (cdr (cdr pair)))))
;; (define (cdaaar pair) (cdr (car (car (car pair)))))
;; (define (cdaadr pair) (cdr (car (car (cdr pair)))))
;; (define (cdadar pair) (cdr (car (cdr (car pair)))))
;; (define (cdaddr pair) (cdr (car (cdr (cdr pair)))))
;; (define (cddaar pair) (cdr (cdr (car (car pair)))))
;; (define (cddadr pair) (cdr (cdr (car (cdr pair)))))
;; (define (cdddar pair) (cdr (cdr (cdr (car pair)))))
;; (define (cddddr pair) (cdr (cdr (cdr (cdr pair)))))

(define (null? obj) (eq? obj '()))

(define (list . lst) lst)

;; (define (length lst) (fold-left (lambda (k lst) (+ k 1)) 0 lst))

;; (define (append . lsts)
;;   (define (append-2 lst1 lst2)
;;     (if (null? lst1)
;; 	lst2
;; 	(cons (car lst1) (append-2 (cdr lst1) lst2))))
;;   (if (null? lsts)
;;       '()
;;       (fold-right append-2 (car lsts) (cdr lsts))))

;; (define (reverse lst)
;;   (fold-left (lambda (result obj) (cons obj result)) '() lst))

;; (define (list-tail lst k)
;;   (if (zero? k)
;;       lst
;;       (list-tail (cdr lst) (- k 1))))

;; (define (list-ref lst k) (car (list-tail lst k)))

;; (define memq #f)
;; (define memv #f)
;; (define member #f)

;; (let ((make-memx (lambda (compare)
;; 		   (define (memx obj lst)
;; 		     (cond ((null? lst) #f)
;; 			   ((compare (car lst) obj) lst)
;; 			   (else (memx obj (cdr lst)))))
;; 		   memx)))
;;   (set! memq (make-memx eq?))
;;   (set! memv (make-memx eqv?))
;;   (set! member (make-memx equal?)))

;; (define assq #f)
;; (define assv #f)
;; (define assoc #f)

;; (let ((make-assx (lambda (compare)
;; 		   (define (assx obj alist)
;; 		     (cond ((null? alist) #f)
;; 			   ((eq? (caar alist) obj) (car alist))
;; 			   (else (assx obj (cdr alist)))))
;; 		   assx)))
;;   (set! assq (make-assx eq?))
;;   (set! assv (make-assx eqv?))
;;   (set! assoc (make-assx equal?)))


;;; 6.3.4 Characters

(define (char=? char1 char2)
  (and (char-ci=? char1 char2)
       (or (and (char-upper-case? char1) (char-upper-case? char2))
	   (not (or (char-upper-case? char1) (char-upper-case? char2))))))
;; (define (char<? char1 char2)
;;   (or (char-ci<? char1 char2)
;;       (and (char-upper-case? char1) (not (char-upper-case? char2)))))
;; (define (char>? char1 char2) (char<? char2 char1))
;; (define (char<=? char1 char2) (not (char>? char1 char2)))
;; (define (char>=? char1 char2) (not (char<? char1 char2)))

;; (define (char-ci<=? char1 char2) (not (char-ci>? char1 char2)))
;; (define (char-ci>=? char1 char2) (not (char-ci<? char1 char2)))

;; (define (char-alphabetic? char)
;;   (and (char-ci<=? #\a char) (char-ci<=? char #\z)))
;; (define (char-numeric? char)
;;   (and (char-ci<=? #\0 char) (char-ci<=? char #\9)))
;; (define (char-whitespace? char) (char-ci=? char #\space))
;; (define (char-lower-case? char)
;;   (and (not (char-upper-case? char)) (char-alphabetic? char)))


;;; 6.3.6 Vectors

(define make-vector
  (let ((old-make-vector make-vector))
    (lambda (k . args)
      (let ((vec (old-make-vector k)))
	(cond ((null? args) vec)
	      ((null? (cdr args))
	       (vector-fill! vec (car args))
	       vec))))))
(define (list->vector lst) (apply vector lst))
(define (vector-fill! vec obj)
  (let ((k (vector-length vec)))
    (do ((i 0 (+ i 1)))
	((= i k))
      (vector-set! vec i obj))))


;;; 6.4 Control features

;; (define (map proc . lsts)
;;   (define (map-1 proc lst)
;;     (if (null? lst)
;; 	'()
;; 	(cons (proc (car lst)) (map-1 proc (cdr lst)))))
;;   (if (null? (car lsts))
;;       '()
;;       (cons (apply proc (map-1 car lsts))
;; 	    (apply map (cons proc (map-1 cdr lsts))))))

(define (fold-left proc obj lst)
  (if (null? lst)
      obj
      (fold-left proc (proc obj (car lst)) (cdr lst))))
(define (fold-right proc obj lst)
  (if (null? lst)
      obj
      (proc (car lst) (fold-right proc obj (cdr lst)))))

;; (define (for-each proc lst)
;;   (if (not (null? lst))
;;       (begin
;; 	(proc (car lst))
;; 	(for-each proc (cdr lst)))))

(define (make-promise thunk)
  (let ((evaluated? #f)
	(value #f))
    (lambda ()
      (if evaluated?
	  value
	  (let ((obj (thunk)))
	    (if evaluated?
		value
		(begin
		  (set! evaluated? #t)
		  (set! value obj)
		  obj)))))))
(define (force promise) (promise))
