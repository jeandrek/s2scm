(define (sieve stream)
  (cons
   (stream-car stream)
   (delay
    (sieve
     (stream-filter (lambda (k)
		      (> (modulo k (stream-car stream)) 0))
		    (stream-cdr stream))))))

(define (add-streams stream1 stream2)
  (cons (+ (stream-car stream1) (stream-car stream2))
	(delay (add-streams (stream-cdr stream1) (stream-cdr stream2)))))

(define (stream-filter pred stream)
  (if (pred (stream-car stream))
      (cons (stream-car stream)
	    (delay (stream-filter pred (stream-cdr stream))))
      (stream-filter pred (stream-cdr stream))))

(define (stream-head stream k)
  (if (zero? k)
      '()
      (cons (stream-car stream) (stream-head (stream-cdr stream) (- k 1)))))

(define (stream-car stream) (car stream))
(define (stream-cdr stream) (force (cdr stream)))

(define ones (cons 1 (delay ones)))
(define naturals (cons 1 (delay (add-streams ones naturals))))
(define primes (sieve (stream-cdr naturals)))

(stream-head primes 5)

