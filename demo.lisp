(print "Hello, Lisp")

(define circle-area (lambda (r) (* 3.14 (* r r))))
(print (circle-area 3.0))

(define twice (lambda (x) (* 2 x)))
(print (twice 5))

(define repeat (lambda (f) (lambda (x) (f (f x)))))
(print ((repeat twice) 10))

(print ((repeat (repeat twice)) 10))
(print ((repeat (repeat (repeat twice))) 10))
(print ((repeat (repeat (repeat (repeat twice)))) 10))

; don't work
; (define fact (lambda (n) (if (<= n 1) 1 (* n (fact (- n 1))))))
; (print (fact 10))
; (print (circle-area (fact 10)))

; don't work
; (define fib (lambda (n) (if (< n 2) 1 (+ (fib (- n 1)) (fib (- n 2))))))
; (print (fib 10))
