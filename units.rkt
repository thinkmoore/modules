#lang racket

(require redex)

(define-language units
  (v ::= (λ (x ...) e) number + -
         (unit (import value-var-decl ...)
               (export value-var-decl ...)
               value-defn ...
               e))
  (e ::= v x (e e ...) (if0 e e e)
         (compound (import value-var-decl ...)
                   (export value-var-decl ...)
                   (link e with (value-var-decl ...) provides (value-var-decl ...))
                   (and e with (value-var-decl ...) provides (value-var-decl ...)))
         (invoke e with (value-invoke-link ...))
         (seq e e) (letrec (value-defn value-defn ...) e))
  (value-defn ::= (val x = e))
  (value-invoke-link ::= (x = e))
  (value-var-decl ::= x)
  (E ::= hole (v ... E e ...) (if0 E e e)
       (compound (import value-var-decl ...)
                 (export value-var-decl ...)
                 (link E with value-var-decl ... provides value-var-decl ...)
                 (and e with value-var-decl ... provides value-var-decl ...))
       (compound (import value-var-decl ...)
                 (export value-var-decl ...)
                 (link v with (value-var-decl ...) provides (value-var-decl ...))
                 (and E with (value-var-decl ...) provides (value-var-decl ...)))
       (invoke E with ((x = e) ...))
       (invoke v with ((x = v) ... (x = E) (x = e) ...))
       (seq E e))
  (x ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  #;(unit (import x_1 ...)
        (export x_2 ...)
        (val x_3 = e_3 #:refers-to (shadow x_1 ...)) ...
        e #:refers-to (shadow x_1 ...))
  (letrec ((val x = e_x) ...) #:refers-to (shadow x ...) e #:refers-to (shadow x ...)))

(define-metafunction units
  subst : e (x ...) (e ...) -> e
  [(subst e () ())
   e]
  [(subst e (x_1 x_2 ...) (e_1 e_2 ...))
   (subst (substitute e x_1 e_1) (x_2 ...) (e_2 ...))])

(define-metafunction units
  letrec-expr : (value-defn ...) e -> e
  [(letrec-expr (value-defn ...) e)
   (letrec (value-defn ...) e)])

(define-judgment-form units
  #:mode (∈ O I)
  #:contract (∈ e (e ...))
  [---------------------
   (∈ e_1 (e_1 e_2 ...))]
  [(∈ e_1 (e_3 ...))
   ---------------------
   (∈ e_1 (e_2 e_3 ...))])

(define-judgment-form units
  #:mode (⊆ I I)
  #:contract (⊆ (e ...) (e ...))
  [--------------
   (⊆ () (e ...))]
  [(∈ e_1 (e_3 ...))
   (⊆ (e_2 ...) (e_3 ...))
   -----------------------------
   (⊆ (e_1 e_2 ...) (e_3 ...))])

(define-judgment-form units
  #:mode (distinct I)
  #:contract (distinct (e ...))
  [----------------------------
   (distinct (e_!_1 ... e_!_1))])

(define units-red
  (reduction-relation
   units
   (--> (in-hole E ((λ (x ..._1) e) v ..._1))
        (in-hole E (subst e (x ...) (v ...)))
        "β")
   (--> (in-hole E (+ number_1 number_2))
        (in-hole E ,(+ (term number_1) (term number_2)))
        "+")
   (--> (in-hole E (- number_1 number_2))
        (in-hole E ,(- (term number_1) (term number_2)))
        "-")
   (--> (in-hole E (if0 0 e_1 e_2))
        (in-hole E e_1)
        "if0-true")
   (--> (in-hole E (if0 number_1 e_1 e_2))
        (in-hole E e_2)
        "if0-false"
        (side-condition (not (= 0 (term number_1)))))
   (--> (in-hole E (compound (import x_i_1 ...)
                             (export x_e_1 ...)
                             (link (unit (import x_i_2 ...)
                                         (export x_e_2 ...)
                                         (val x_d_2 = e_d_2)
                                         ...
                                         e_2)
                                   with (x_w_2 ...) provides (x_p_2 ...))
                             (and  (unit (import x_i_3 ...)
                                         (export x_e_3 ...)
                                         (val x_d_3 = e_d_3)
                                         ...
                                         e_3)
                                   with (x_w_3 ...) provides (x_p_3 ...))))
        (in-hole E (unit (import x_i_1 ...)
                         (export x_e_1 ...)
                         (val x_d_2 = e_d_2)
                         ...
                         (val x_d_3 = e_d_3)
                         ...
                         (seq e_2 e_3)))
        (judgment-holds (⊆ (x_i_2 ...) (x_w_2 ...)))
        (judgment-holds (⊆ (x_p_2 ...) (x_e_2 ...)))
        (judgment-holds (⊆ (x_i_3 ...) (x_w_3 ...)))
        (judgment-holds (⊆ (x_p_3 ...) (x_e_3 ...)))
        (judgment-holds (distinct (x_i_1 ... x_d_2 ... x_d_3 ...)))
        "compound")
   (--> (in-hole E (invoke (unit (import x_i ...)
                                 (export x_e ...)
                                 (val x_d = e_d)
                                 ...
                                 e_b) with ((x_w = v_w) ...)))
        (in-hole E (subst (letrec ((val x_d = e_d) ...)
                            e_b)
                          (x_w ...)
                          (v_w ...)))
        (judgment-holds (⊆ (x_i ...) (x_w ...)))
        "invoke")
   (--> (in-hole E (seq v e))
        (in-hole E e)
        "seq")
   (--> (in-hole E (letrec ((val x_1 = e_1) ...) e_b))
        (in-hole E (subst e_b (x_1 ...) ((letrec-expr ((val x_1 = e_1) ...) e_1) ...)))
        "letrec")))

(define letrec-test
  (term (letrec ((val even? = (λ (x) (if0 x 1 (odd?  (- x 1)))))
                 (val odd?  = (λ (x) (if0 x 0 (even? (- x 1))))))
          (even? 3))))

(define unit-test
  (term (invoke (compound (import)
                          (export)
                          (link (unit (import odd?)
                                      (export even?)
                                      (val even? = (λ (x) (if0 x 1 (odd?  (- x 1)))))
                                      0)
                                with (odd?) provides (even?))
                          (and  (unit (import even?)
                                      (export odd?)
                                      (val odd?  = (λ (x) (if0 x 0 (even? (- x 1)))))
                                      (even? 4))
                                with (even?) provides (odd?)))
                with ())))

(define compound-test
  (term (compound (import)
                  (export)
                  (link (unit (import odd?)
                              (export even?)
                              (val even? = (λ (x) (if0 x 1 (odd?  (- x 1)))))
                              0)
                        with (odd?) provides (even?))
                  (and  (unit (import even?)
                              (export odd?)
                              (val odd?  = (λ (x) (if0 x 0 (even? (- x 1)))))
                              (even? 4))
                        with (even?) provides (odd?)))))

(define shadow-test
  (term ((λ (odd?)
          (compound (import)
                  (export)
                  (link (unit (import odd?)
                              (export even?)
                              (val even? = (λ (x) (if0 x 1 (odd?  (- x 1)))))
                              0)
                        with (odd?) provides (even?))
                  (and  (unit (import even?)
                              (export odd?)
                              (val odd?  = (λ (x) (if0 x 0 (even? (- x 1)))))
                              (even? 4))
                        with (even?) provides (odd?))))
         (λ (x) 42))))