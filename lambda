#lang racket
#|
 <exp> ::= <var>

        |  #t
        |  #f
        |  (if  <exp> <exp> <exp>)
        |  (and <exp> <exp>)
        |  (or  <exp> <exp>)
        |  (not <exp>)

        |  <nat>
        |  (zero? <exp>)
        |  (- <exp> <exp> ...)
        |  (= <exp> <exp>)
        |  (+ <exp> <exp> ...)
        |  (* <exp> <exp> ...)
        |  (^ <exp> <exp>)
        |  (/ <exp> <exp>)
        |  (<= <exp> <exp>)
        |  (>= <exp> <exp>)
        |  (< <exp> <exp>)
        |  (> <exp> <exp>)
        |  (!= <exp> <exp>)

        |  <lam>
        |  (let ((<var> <exp>) ...) <exp>)
        |  (letrec ((<var> <lam>)) <exp>)

        |  (cons <exp> <exp>)
        |  (car  <exp>)
        |  (cdr  <exp>)
        |  (pair? <exp>)
        |  (null? <exp>)
        |  '()

        |  (<exp> <exp> ...)

 <lam> ::= (lambda (<var> ...) <exp>)
|#

(define VOID
  `(lambda (_) _))


(define TRUE
  `(lambda (t)
     (lambda (f)
       (t ,VOID))))

(define FALSE
  `(lambda (t)
     (lambda (f)
       (f ,VOID))))

; church-numeral
(define ZERO `(lambda (f) (lambda (x) x)))

(define PRED
  `(lambda (n)
     (lambda (f)
       (lambda (x)
         (((n (lambda (g)
                (lambda (h)
                  (h (g f)))))
           (lambda (u) x))
          (lambda (u) u))))))

(define PLUS
  `(lambda (a)
     (lambda (b)
       (lambda (f)
         (lambda (x)
           ((a f) ((b f) x)))))))

(define MUL
  `(lambda (a)
     (lambda (b)
       (lambda (f)
         (lambda (x)
           ((a (b f)) x))))))

(define EXP
  `(lambda (a)
     (lambda (b)
       (b a))))

(define MINUS
  `(lambda (a)
     (lambda (b)
       ((b ,PRED) a))))

(define (church-numeral n)
  (define (apply-n f n x)
    (if (= n 0) x `(,f ,(apply-n f (- n 1) x))))
  `(lambda (f)
     (lambda (x)
       ,(apply-n 'f n 'x))))

(define CONS
  `(lambda (a)
     (lambda (b)
       (lambda (on-cons)
         (lambda (on-nil)
           ((on-cons a) b))))))
(define NULL
  `(lambda (on-cons)
     (lambda (on-nil)
       (on-nil ,VOID))))

(define CAR
  `(lambda (p)
     ((p (lambda (a) (lambda (b) a)))
      ,VOID)))

(define CDR
  `(lambda (p)
     ((p (lambda (a) (lambda (b) b)))
      ,VOID)))

(define Y
  `(lambda (f)
     ((lambda (x)
        (f (lambda (_) ((x x) _))))
      (lambda (x)
        (f (lambda (_) ((x x) _)))))))

(define STRING
  `(lambda (s)
     (lambda (on-s)
       (lambda (on-empty)
         (on-s s)))))

(define EMPTY
  `(lambda (on-s)
     (lambda (on-empty)
       (on-empty ,VOID))))


; Symble Table
(define (make-st)
  (make-immutable-hash))

(define (st-add st s)
  (hash-set st s null))

(define (st-add-all st symbols)
  (match symbols
    ['() st]
    [`(,x ,xs ...) (st-add-all (st-add st x) xs)]))

(define (st-has st s)
  (hash-has-key? st s))

(define (compile1-application expr st)
  (match expr
    [`(,f)
     `(,(compile0 f st) ,VOID)]
    [`(,f ,arg)
     `(,(compile0 f st) ,(compile0 arg st))]
    [`(,f ,arg ,args ...)
     (compile0 `((,f ,arg) ,@args) st)]
    [else
     (error (format "unknow exp: ~s" expr))]))

(define (compile1 expr st)
  (match expr
    ; Var
    [(or 'null 'nil) NULL]
    [(? symbol?) expr]

    ; Boolean
    [`#t TRUE]
    [`#f FALSE]

    ; Conditional
    [`(if ,cond ,t ,f)
     `((,(compile0 cond st)
        (lambda (_) ,(compile0 t st)))
       (lambda (_) ,(compile0 f st)))]
    [`(and ,a ,b)
     (compile0 `(if ,a ,b #f) st)]
    [`(and ,a ,b ,rest ...)
     (compile0 `(and (and ,a ,b) ,@rest) st)]
    [`(or ,a ,b)
     (compile0 `(if ,a #t ,b) st)]
    [`(or ,a ,b ,rest ...)
     (compile0 `(or (or ,a ,b) ,@rest) st)]
    [`(not ,a)
     (compile0 `(if ,a #f #t) st)]

    ; Number
    [(? integer?)
     (church-numeral expr)]
    [`(zero? ,n)
     `((,(compile0 n st) (lambda (_) ,FALSE)) ,TRUE)]

    ; Arithmatic
    [`(+ ,a ,b)
     `((,PLUS ,(compile0 a st)) ,(compile0 b st))]
    [`(+ ,a ,b ,rest ...)
     (compile0 `(+ (+ ,a ,b) ,@rest) st)]
    [`(- ,a ,b)
     `((,MINUS ,(compile0 a st)) ,(compile0 b st))]
    [`(- ,a ,b ,rest ...)
     (compile0 `(- (- ,a ,b) ,@rest) st)]
    [`(* ,a ,b)
     `((,MUL ,(compile0 a st)) ,(compile0 b st))]
    [`(* ,a ,b ,rest ...)
     (compile0 `(* (* ,a ,b) ,@rest) st)]
    [`(/ ,a ,b)
     (compile0 `(letrec ((div (lambda (m n)
                                (if (>= m n)
                                    (+ 1 (div (- m n) n)) 0))))
                  (div ,a ,b)) st)]
    [`(/ ,a ,b ,rest ...)
     (compile0 `(/ (/ ,a ,b) ,@rest) st)]
    [`(% ,a ,b)
     (compile0 `(- ,a (* (/ ,a ,b) ,b)) st)]
    [`(^ ,a ,b)
     `((,EXP ,(compile0 a st)) ,(compile0 b st))]
    [`(= ,a ,b)
     (compile0 `(and (zero? (- ,a ,b)) (zero? (- ,b ,a))) st)]
    [`(!= ,a ,b)
     (compile0 `(not (= ,a ,b)) st)]
    [`(>= ,a ,b)
     (compile0 `(or (> ,a ,b) (= ,a ,b)) st)]
    [`(<= ,a ,b)
     (compile0 `(or (< ,a ,b) (= ,a ,b)) st)]
    [`(> ,a ,b)
     (compile0 `(and (!= ,a ,b) (zero? (- ,b ,a))) st)]
    [`(< ,a ,b)
     (compile0 `(and (!= ,a ,b) (zero? (- ,a ,b))) st)]

    ;Pair
    [''() NULL]
    [`(null? ,a)
     `((,(compile0 a st)
        (lambda (_) (lambda (_) ,FALSE)))
       (lambda (_) ,TRUE))]
    [`(cons ,a ,b)
     `((,CONS ,(compile0 a st)) ,(compile0 b st))]
    [`(car ,p)
     `(,CAR ,(compile0 p st))]
    [`(cdr ,p)
     `(,CDR ,(compile0 p st))]
    [`(pair? ,a)
     `((,(compile0 a st)
        (lambda (_) (lambda (_) ,TRUE)))
       (lambda (_) ,FALSE))]
    [`(list) NULL]
    [`(list ,a)
     (compile0 `(cons ,a null) st)]
    [`(list ,a ,as ...)
     (compile0 `(cons ,a (list ,@as)) st)]


    ; String
    ['"" EMPTY]
    [(? string?)
     (define (to-ints s)
       (if (non-empty-string? s)
           (cons (church-numeral (char->integer (string-ref s 0)))
                 (to-ints (substring s 1)))
           '()))
     `(,STRING ,(compile0 `(list ,@(to-ints expr)) st))]
    [`(empty-string? ,a)
     `((,(compile0 a st) (lambda (s) ,FALSE))
       (lambda (_) ,TRUE))]
    [`(non-empty-string? ,a)
     (compile0 `(not (empty-string? ,a)) st)]
    [`(~s ,x)
     `(,STRING ,(compile0 `(letrec ((to (lambda (n lst)
                                          (if (= n 0)
                                              lst
                                              (let ((nn (/ n 10))
                                                    (m (% n 10)))
                                                (to nn (cons (+ m 48) lst)))))))
                            (to ,x '())) st))]


    ; Lambda
    [`(lambda () ,body)
     `(lambda (_) ,(compile0 body st))]
    [`(lambda (,arg) ,body)
     `(lambda (,arg) ,(compile0 body (st-add st arg)))]
    [`(lambda (,arg ,args ...) ,body)
     `(lambda (,arg) ,(compile0 `(lambda (,@args) ,body) (st-add st arg)))]
    [`(let ((,var ,exp) ...) ,body)
     (compile0 `((lambda (,@var) ,body) ,@exp) st)]

    ; Recursion
    [`(letrec ((,f ,exp)) ,body)
     (compile0 `(let ((,f (,Y (lambda (,f) ,exp)))) ,body) st)]

    [else (compile1-application expr st)]))

(define (compile0 expr st)
  (if (st-has st 'lambda)
      (error "keyword lambda can't be used as variable name.")
      (match expr
        [`(,f ,_ ...) #:when (st-has st f)
                      (compile1-application expr st)]
        [else (compile1 expr st)])))

(define (compile expr) (compile0 expr (make-st)))


; Tests
(define (succ n) (+ n 1))

(define (intify church-num)
  ((church-num succ) 0))

(define (boolify church-bool)
  ((church-bool (lambda (_) #t)) (lambda (_) #f)))

(define (listify f church-list)
  ((church-list
    (lambda (a) (lambda (b) (cons (f a) (listify f b)))))
   (lambda (_) null)))
(define (stringify church-string)
  ((church-string
    (lambda (x)
      (list->string
       (map integer->char
            (listify intify x)))))
   (lambda (_) "")))


(define ns (make-base-namespace))

(define (run code)
  (eval code ns))

(define (run->bool code)
  (boolify (run (compile code))))

(define (run->int code)
  (intify (run (compile code))))

(define (run->list-int code)
  (listify intify (run (compile code))))

(define (run->list-string code)
  (listify stringify (run (compile code))))

(define (run->string code)
  (stringify (run (compile code))))

(require rackunit)
(require rackunit/text-ui)

(define all-tests
  (test-suite
   "Tests"
   (test-case
    "Numeral"
    (for ([i (in-range 20)])
      (check-equal? (run->int i) i (format "failed number is: ~s" i)))
    (check-equal? (run->bool '(zero? 0)) #t)
    (check-equal? (run->bool '(zero? 1)) #f)
    (check-equal? (run->bool '(zero? (+ 1 2))) #f))
   (test-case
    "Boolean"
    (check-equal? (run->bool #t) #t)
    (check-equal? (run->bool #f) #f))
   (test-case
    "Pair & List"
    (check-equal? (run->bool '(null? null)) #t)
    (check-equal? (run->bool '(null? (cons 1 1))) #f)
    (check-equal? (run->bool '(pair? (cons 1 1))) #t)
    (check-equal? (run->int '(car (cons 1 2))) 1)
    (check-equal? (run->int '(car (cons (+ 1 2) (+ 2 3)))) 3)
    (check-equal? (run->int '(cdr (cons (+ 1 2) (+ 2 5)))) 7)
    (check-equal? (run->list-int '(cdr (cons 1 (cons 2 (cons 3 null))))) '(2 3))
    (check-equal? (run->list-int '(list)) null)
    (check-equal? (run->list-int '(list 1 2 3 4 5)) '(1 2 3 4 5)))
   (test-case
    "Arithmatic"
    (check-equal? (run->int '(+ 1 2)) 3)
    (check-equal? (run->int '(+ 1 (+ 1 (+ 1 1 1 0 0 0)))) 5)
    (check-equal? (run->int '(- 5 2)) 3)
    (check-equal? (run->int '(- 1 (- 1 (- 2 1 1 0 0 0)))) 0)
    (check-equal? (run->int '(* 2 2)) 4)
    (check-equal? (run->int '(* 1 (* 1 (* 1 1 1 1 2)))) 2)
    (check-equal? (run->int '(^ 2 3)) 8)
    (check-equal? (run->int '(^ 2 10)) 1024)
    (check-equal? (run->bool '(zero? 0)) #t)
    (check-equal? (run->bool '(zero? 1)) #f)
    (check-equal? (run->bool '(zero? 2)) #f)
    (check-equal? (run->bool '(> 2 1)) #t)
    (check-equal? (run->bool '(> 1 2)) #f)
    (check-equal? (run->bool '(> (+ 1 1) (+ 1 0))) #t)
    (check-equal? (run->bool '(> (+ 1 0) (+ 1 1))) #f)
    (check-equal? (run->bool '(< 1 2)) #t)
    (check-equal? (run->bool '(< 2 1)) #f)
    (check-equal? (run->bool '(< (- 2 1) (- 3 1))) #t)
    (check-equal? (run->bool '(< (- 3 1) (- 2 1))) #f)
    (check-equal? (run->bool '(= 1 1)) #t)
    (check-equal? (run->bool '(= 1 2)) #f)
    (check-equal? (run->bool '(= (+ 1 2) (* 1 3))) #t)
    (check-equal? (run->bool '(= (+ 1 2) (* 1 4))) #f)
    (check-equal? (run->bool '(!= 3 2)) #t)
    (check-equal? (run->bool '(!= 2 2)) #f)
    (check-equal? (run->bool '(!= (- 4 1) (+ 1 1))) #t)
    (check-equal? (run->bool '(!= (- 4 1) (+ 2 1))) #f)
    (check-equal? (run->bool '(<= (- 2 1) (* 1 1))) #t)
    (check-equal? (run->bool '(<= (+ 0 0) (* 1 1))) #t)
    (check-equal? (run->bool '(<= (+ 5 0) (* 1 1))) #f)
    (check-equal? (run->bool '(>= (+ 1 2) (+ 1 1))) #t)
    (check-equal? (run->bool '(>= (+ 2 2) (+ 1 3))) #t)
    (check-equal? (run->bool '(>= (+ 2 1) (+ 1 3))) #f)
    (check-equal? (run->int '(/ (+ 2 2) (+ 1 1))) 2)
    (check-equal? (run->int '(/ (+ 4 4) (+ 1 1) (+ 1 1))) 2))
   (test-case
    "Conditional"
    (check-equal? (run->bool '(if #t #f #t)) #f)
    (check-equal? (run->int '(if (< 3 2) (+ 1 2) (+ 1 3))) 4)
    (check-equal? (run->bool '(and #t #f)) #f)
    (check-equal? (run->bool '(and #t #t)) #t)
    (check-equal? (run->bool '(and #f #f)) #f)
    (check-equal? (run->bool '(and #t #f #t #t #t)) #f)
    (check-equal? (run->bool '(and #t #t #t #t #t)) #t)
    (check-equal? (run->bool '(and (> 2 1) (> 3 2) (> 4 3))) #t)
    (check-equal? (run->bool '(or #t #t)) #t)
    (check-equal? (run->bool '(or #f #t)) #t)
    (check-equal? (run->bool '(or #f #f)) #f)
    (check-equal? (run->bool '(or #f #f)) #f)
    (check-equal? (run->bool '(or #f #f #f #f #t)) #t)
    (check-equal? (run->bool '(or #f #f #f #f #f)) #f)
    (check-equal? (run->bool '(or (> 1 2) (> 2 3) (> 3 4))) #f)
    (check-equal? (run->bool '(not #t)) #f)
    (check-equal? (run->bool '(not (< 1 2))) #f)
    (check-equal? (run->bool '(not (> 1 2))) #t))
   (test-case
    "Lambda"
    (check-equal? (run->int '((lambda () (+ 2 1)) 5)) 3)
    (check-equal? (run->int '((lambda (a) (+ a 1)) 3)) 4)
    (check-equal? (run->int '((lambda (a b) (+ a b)) 1 2)) 3)
    (check-equal? (run->int '((lambda (a b c d) (+ a b c d)) 1 2 3 4)) 10))
   (test-case
    "Let & Letrec"
    (check-equal? (run->int '(let ((a 1)) (+ a 1))) 2)
    (check-equal? (run->int '(let ((a 1) (b 2)) (+ a b))) 3)
    (check-equal? (run->int '(let ((add1 (lambda (a) (+ a 1)))
                                   (add2 (lambda (a) (+ a 2))))
                               (add1 (add2 2)))) 5)
    (check-equal? (run->int '(letrec ((fac
                                       (lambda (n)
                                         (if (= n 0)
                                             1
                                             (* n (fac (- n 1)))))))
                               (fac 5))) 120)
    (check-equal? (run->int '(letrec ((fib
                                       (lambda (n a b)
                                         (if (= n 1)
                                             a
                                             (fib (- n 1) b (+ a b))))))
                               (fib 10 0 1))) 34))
   (test-case
    "String"
    (check-equal? (run->string '"123") "123")
    (check-equal? (run->string '"Hello World!") "Hello World!")
    (check-equal? (run->string '"") "")
    (check-equal? (run->bool '(non-empty-string? "")) #f)
    (check-equal? (run->bool '(empty-string? "13")) #f)
    (check-equal? (run->string '(~s 123)) "123")
    (check-equal? (run->string '(~s (+ 1 2))) "3"))

   (test-case
    "Fizzbuzz"
    (check-equal? (run->list-string `(letrec ((fizzbuzz (lambda (n lst)
                                                          (if (= n 0)
                                                              lst
                                                              (if (zero? (% n 15))
                                                                  (fizzbuzz (- n 1) (cons "Fizz Buzz" lst))
                                                                  (if (zero? (% n 5))
                                                                      (fizzbuzz (- n 1) (cons "Buzz" lst))
                                                                      (if (zero? (% n 3))
                                                                          (fizzbuzz (- n 1) (cons "Fizz" lst))
                                                                          (fizzbuzz (- n 1) (cons (~s n) lst)))))))))
                                       (fizzbuzz 20 nil)))
                  '("1" "2" "Fizz" "4" "Buzz" "Fizz" "7" "8" "Fizz" "Buzz" "11" "Fizz" "13" "14" "Fizz Buzz" "16" "17" "Fizz" "19" "Buzz")))


   (test-case
    "Corner Case"
    (check-equal? (run->int '(let ((if (lambda (a b c) (+ a b c)))
                                   (and (lambda (a b) (+ a b))))
                               (if 1 2 (and 1 2)))) 6)
    (check-equal? (run->int '((lambda (if -)
                                (if 1 2 (- 1 2)))
                              (lambda (a b c) (+ a b c))
                              (lambda (a b) (+ a b)))) 6)
    (check-exn exn:fail? (lambda ()
                           (run->int '((lambda (lambda) 1) 1)))))))


(define _ (run-tests all-tests 'verbose))
