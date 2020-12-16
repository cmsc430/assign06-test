#lang racket
(require "../interp.rkt" ; CHANGED THIS, ORIGINALLY POINTED TO ./interp.rkt, which doesn't have updated ast
         rackunit)

(define (read-prog p)
  (regexp-match "^#lang racket" p)
  (sexpr->prog (read p))) ; use sexpr to prog function here to work with new AST representation

;; Code for submission needs to be in ".." directory
(require (only-in "../compile.rkt" compile)
         (only-in "../asm/interp.rkt" asm-interp)
         (only-in "../syntax.rkt" sexpr->prog sexpr->expr prog? expr? closed?))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Syntax tests


; made wrapper functions with the correct conversions
(define (check-expr? p) (expr? (sexpr->expr p))) ; use sexpr->expr because these are pre-Iniquity examples
(define (check-prog? p) (prog? (sexpr->prog p)))
(define (check-closed? p) (closed? (sexpr->prog p)))

(check-true (check-expr? 7))
(check-true (check-expr? "asdf"))
(check-true (check-expr? ""))
(check-true (check-expr? #t))
(check-true (check-expr? #t))
(check-true (check-expr? #\a))
(check-true (check-expr? '(add1 #f)))
(check-true (check-expr? '(sub1 #f)))
(check-true (check-expr? '(abs #f)))
(check-true (check-expr? '(- #f)))
(check-true (check-expr? '(zero? #f)))
(check-true (check-expr? '(integer->char #f)))
(check-true (check-expr? '(char->integer #f)))
(check-true (check-expr? '(char? #f)))
(check-true (check-expr? '(integer? #f)))
(check-true (check-expr? '(boolean? #f)))
(check-true (check-expr? '(box "adsf")))
(check-true (check-expr? '(+ 1 2)))
(check-true (check-expr? '(- 1)))
(check-true (check-expr? '(- 1 2)))
(check-true (check-expr? 'x))
(check-true (check-expr? '(let () x)))
(check-true (check-expr? '(let ((x 1)) x)))
(check-true (check-expr? '(let ((x 1) (y 2)) x)))
(check-true (check-expr? '(let ((x 1) (y 2) (z 3)) x)))
(check-true (check-expr? '(string-length "asdf")))
(check-true (check-expr? '(string-ref "asdf" 0)))
(check-true (check-expr? '(= #f #f)))
(check-true (check-expr? '(< #f #f)))
(check-true (check-expr? '(string? #f)))
(check-true (check-expr? '(box? #f)))
(check-true (check-expr? '(empty? #f)))
(check-true (check-expr? '(cons? #f)))
(check-true (check-expr? '(unbox #f)))
(check-true (check-expr? '(car #f)))
(check-true (check-expr? '(cdr #f)))
(check-true (check-expr? '(make-string #f #f)))
(check-true (check-expr? '(= #f #f)))
(check-true (check-expr? '(< #f #f)))
(check-true (check-expr? '(<= #f #f)))
(check-true (check-expr? '(char=? #f #f)))
(check-true (check-expr? '(boolean=? #f #f)))
(check-true (check-expr? '(+ #f #f)))
(check-true (check-expr? '(- #f #f)))


; I commented these out, but I think you just need to convert these to how you had them in assign05-test 
;;; (check-false (check-expr? '(let 1)))        ;; for instance, this becomes (check-exn exn:fail? (lambda () (expr? (sexpr->expr '(let 1)))))
(check-exn exn:fail? (lambda () (expr? (sexpr->expr '(let 1)))))
;;; (check-false (check-expr? '(let x 1)))
;;; (check-false (check-expr? '(let x y 1)))
;;; (check-false (check-expr? '(let (x y) 1)))
;;; (check-false (check-expr? '(let ((x)) 1)))
;;; (check-false (check-expr? '(let ((1 2)) 1)))
;;; (check-false (check-expr? '(let ((abs 1)) 1)))
;;; (check-false (check-expr? '(let ((string-ref 1)) 1)))
;;; (check-false (check-expr? '(let ((+ 1)) 1)))
;;; (check-false (check-expr? '(let ((string? 1)) 1)))
;;; (check-false (check-expr? '(1)))
;;; (check-false (check-expr? '(box)))
;;; (check-false (check-expr? '(string-ref "asdf")))
;;; (check-false (check-expr? '(+ 1 2 3)))
;;; (check-false (check-expr? '(make-string #f)))
;;; (check-false (check-expr? '(make-string #f #f #f)))

(check-true (check-prog? 5))
(check-true (check-prog? '(begin (define (f x) x)
                           (f 5))))
(check-true (check-prog? '(begin (define (f x y z) x)
                           (f 5 6 7))))
(check-true (check-prog? '(begin (define (f x y z) (g x))
                           (define (g q) q)
                           (f 5 6 7))))

; LISP 1 vs LISP 2, we fall back on Racket's conventions!
(check-true (check-prog? '(begin (define (f f) f)
                            (f 5))))



(check-true (check-closed? 7))
(check-true (check-closed? "asdf"))
(check-true (check-closed? ""))
(check-true (check-closed? #t))
(check-true (check-closed? #f))
(check-true (check-closed? #\a))
(check-true (check-closed? '(box "adsf")))
(check-true (check-closed? '(+ 1 2)))
(check-true (check-closed? '(- 1)))
(check-true (check-closed? '(- 1 2)))
(check-true (check-closed? '(let ((x 1)) x)))
(check-true (check-closed? '(let ((x 1) (y 2)) x)))
(check-true (check-closed? '(let ((x 1) (y 2) (z 3)) x)))
(check-true (check-closed? '(string-length "asdf")))
(check-true (check-closed? '(string-ref "asdf" 0)))
(check-true (check-closed? '(let ((x 1) (y 2))
                        (let ((z y))
                          (+ x z)))))

(check-false (check-closed? 'x))
(check-false (check-closed? '(let () x)))
(check-false (check-closed? '(let ((x 1)) y)))
(check-false (check-closed? '(let ((x 1) (y x)) y)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Compiler tests

(define (run p)
  (asm-interp (compile (sexpr->prog p))))

(check-equal?
 (run '(let ((x 1)) x))
 (interp (sexpr->prog '(let ((x 1)) x))))

(check-equal? (run
               '(begin (define (f x) x)
                       (f 5)))
              5)

(check-equal? (run
               '(begin (define (tri x)
                         (if (zero? x)
                             0
                             (+ x (tri (sub1 x)))))
                       (tri 9)))
              45)

(check-equal? (run
               '(begin (define (even? x)
                         (if (zero? x)
                             #t
                             (odd? (sub1 x))))
                       (define (odd? x)
                         (if (zero? x)
                             #f
                             (even? (sub1 x))))
                       (even? 101)))
              #f)

(check-equal? (run
               '(begin (define (map-add1 xs)
                         (if (empty? xs)
                             '()
                             (cons (add1 (car xs))
                                   (map-add1 (cdr xs)))))
                       (map-add1 (cons 1 (cons 2 (cons 3 '()))))))
               '(2 3 4))

(check-equal? (run
               '(begin
                  (define (explode str)
                    (explode/i str 0))
                  (define (explode/i str i)
                    (if (= (string-length str) i)
                        '()
                        (cons (string-ref str i)
                              (explode/i str (add1 i)))))
                  (explode "fred")))
              '(#\f #\r #\e #\d))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Random tests

(define parses
  (parameterize ((current-directory "progs"))
    (for/list ([fn (directory-list)])
      (list fn (call-with-input-file fn read-prog)))))

(for ([p parses])
  (match p
    [(list fn p)
     (check-true (and (prog? p)
                      (closed? p))
                 (list fn p))]))

(for ([p parses])
  (match p
    [(list fn p)
     (check-equal? (with-handlers ([exn:fail? identity])
                     (asm-interp (compile p)))
                   (interp p)
                   (list fn p))]))
