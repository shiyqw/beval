;;;;;;;;;;;;;;;;;;;;;kernel;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;meval
(define (meval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((quoted? exp) (text-of-quotation exp))
        ((assignment? exp) (eval-assignment exp env))
        ((definition? exp) (eval-definition exp env))
        ((if? exp) (eval-if exp env))
        ((lambda? exp)
         (make-procedure (lambda-parameters exp)
                         (lambda-body exp)
                         env))
        ((begin? exp)
         (eval-sequence (begin-actions exp) env))
        ((cond? exp) (meval (cond->if exp) env))
        ((and? exp) (meval (and->if exp) env))
        ((or? exp) (meval (or->if exp) env))
        ((let? exp) (meval (let->combination exp) env))
        ((let*? exp) (meval (let*->nested-lets exp) env))
        ((while? exp) (meval (while->combination  exp) env)) 
        ((map? exp) (meval (map->combination exp) env))
        ((application? exp)
         (mapply (meval (operator exp) env)
                 (list-of-values (operands exp) env)))
        (else
         (error "Unknown expression type -- EVAL" exp))))


;mapply
(define (mapply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((compound-procedure? procedure)
         (eval-sequence 
            (procedure-body procedure)
            (extend-environment
               (procedure-parameters procedure)
               arguments
               (procedure-environment procedure))))
        (else 
         (error "Unknown procedure type -- APPLY" procedure))))

;meval's inner implement
(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (meval (first-operands exps) env)
            (list-of-values (rest-operands exps) env))))

(define (eval-if exp env)
  (if (true? (meval (if-predicate exp) env))
      (meval (if-consequent exp) env)
      (meval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (meval (first-exp exps) env))
        (else (meval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (meval (assignment-value exp) env)
                       env)
  'ok)

(define (eval-definition exp env)
  (define-variable! (definition-variable exp)
                    (meval (definition-value exp) env)
                    env)
  'ok)

;;;;;;;;;;;;;;;;;basic data structure;;;;;;;;;;;;;;;;;;;;;;
;self-evaluating
(define (self-evaluating? exp)
  (cond ((number? exp) true)
        ((string? exp) true)
        (else false)))

(define (variable? exp) (symbol? exp))

;quotation
(define (quoted? exp)
  (tagged-list? exp 'quote))
(define (text-of-quotation exp)
  (cadr exp))
(define (tagged-list? exp tag)
   (if (pair? exp)
       (eq? (car exp) tag)
       false))

;assignment
(define (assignment? exp)
  (tagged-list? exp 'set!))
(define (assignment-variable exp) (cadr exp))
(define (assignment-value exp) (caddr exp)) 

;definition
(define (definition? exp)
  (tagged-list? exp 'define))
(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))
(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

;lambda
(define (lambda? exp) (tagged-list? exp 'lambda))
(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))
(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;if
(define (if? exp) (tagged-list? exp 'if))
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))
(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

;begin
(define (begin? exp) (tagged-list? exp 'begin))
(define (begin-actions exp) (cdr exp))
(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))
(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))
(define (make-begin seq) (cons 'begin seq))

;application
(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))
(define (no-operands? ops) (null? ops))
(define (first-operands ops) (car ops))
(define (rest-operands ops) (cdr ops))

;cond
(define (cond? exp) (tagged-list? exp 'cond))
(define (cond-clauses exp) (cdr exp))
(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))
(define (cond-predicate clause) (car clause))
(define (cond-actions clause) (cdr clause))
(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF" clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

;;;;;;;;;;;;;;;;;;;;advanced data structure;;;;;;;;;;;;;;;;;;;
;predication check
(define (true? x)
  (not (eq? x false)))
(define (false? x)
  (eq? x false))

;procedure
(define (make-procedure parameters body env)
  (list 'procedure parameters (scan-out-defines body) env))
(define (compound-procedure? p)
  (tagged-list? p 'procedure))
(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

(define (scan-out-defines body)
  (let ((let-body '())
        (set-body '())
        (others '()))
    (let scan-iter ((b body))
      (cond ((null? b) '())
            ((definition? (car b))
             (let ((def-var (definition-variable (car b)))
                   (def-val (definition-value (car b))))
               (set! let-body (cons (list def-var "*unassigned*")
                                    let-body))
               (set! set-body (cons (cons 'set! (list def-var
                                                      def-val))
                                    set-body))))
            (else (set! others (append others (list (car b))))))
      (if (not (null? b))
          (scan-iter (cdr b))
          'false))
    (if (null? let-body)
        body
        (list (append (list 'let let-body)
                      (append set-body others))))))

;environment
(define (enclosing-environment env) (cdr env))
(define (first-frame env) (car env))
(define the-empty-environment '())
(define (make-frame variables values)
  (cons variables values))
(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))
(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

(define (extend-environment vars vals base-env)
  (if (= (length vals) (length vars))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (if (eq? (car vals) "*unassigned*")
                 (error "Unassigned variable" var)
                 (car vals)))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars) 
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

;;;;;;;;;;;;;;;;;running as a program;;;;;;;;;;;;;;;;;;;
(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    initial-env))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))
(define (primitive-implementation proc) (cadr proc))

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '/ /)
        (list '= =)
        (list '< <)
        (list '> >)
        (list 'display display)
        (list 'newline newline)
        ;(list 'map map)
        ;<other>
        ))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))

(define (primitive-procedure-names)
  (map car 
       primitive-procedures))

(define (apply-primitive-procedure proc args)
  (apply 
   (primitive-implementation proc) args))

;driver loop
(define input-prompt ":::M-Eval input:")
(define output-prompt ":::M-Eval output:")

(define (prompt-for-input string)
  (newline)
  (newline)
  (display string)
  (newline))

(define (announce-output string)
  (newline)
  (display string)
  (newline))

(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
;    (let ((output (meval input the-global-environment)))
      (define start-time (get-universal-time))
      (define output (meval input the-global-environment))
      (announce-output output-prompt)
      (user-print output)
      (newline)
      (display "using time: ")
      (display (- (get-universal-time) start-time))
      (newline))
  (driver-loop))


(define (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))

;error & true & false
(define (error reason . args)
  (display "Error: ")
  (display reason)
      (for-each (lambda (arg) 
                  (display " ")
		  (write arg))
		args)
      (newline)
      (scheme-report-environment -1))

(define true #t)
(define false #f)

;;;;;;;;;;;;;;;;;;;;;extentions;;;;;;;;;;;;;;;;;;;;;;;;;;
;and & or
(define (and? exp) (tagged-list? exp 'and))
(define (or? exp) (tagged-list? exp 'or))

(define (and->if exp)
  (let ((and-operands (cdr exp)))
    (expand-and-operands and-operands)))
(define (expand-and-operands operands)
  (if (null? operands)
      'true
      (make-if (car operands)
               (expand-and-operands (cdr operands))
               'false)))

(define (or->if exp)
  (let ((or-operands (cdr exp)))
    (expand-or-operands or-operands)))
(define (expand-or-operands operands)
  (if (null? operands)
      'false
      (make-if (car operands)
               'true
               (expand-or-operands (cdr operands)))))
    
;let
(define (let? exp) (tagged-list? exp 'let))
(define (let-variables exp) (map car (cadr exp)))
(define (let-values exp) (map cadr (cadr exp)))
(define (let-body exp) (cddr exp))


(define (let*? exp) (tagged-list? exp 'let*))
(define (let*-variables exp) (map car (cadr exp)))
(define (let*-values exp) (map cadr (cadr exp)))
(define (let*-assignment exp) (cadr exp))
(define (let*-body exp) (cddr exp))
(define (let*->nested-lets exp)
  (define (transform-let* assignment body)
    (if (null? (cdr assignment))
        (cons 'let (cons assignment body))
        (list 'let (list (car assignment))
                   (transform-let* (cdr assignment)
                                   body))))
  (transform-let* (let*-assignment exp) (let*-body exp)))

;named-let
(define (named-let? exp) (and (let? exp) (symbol? (cadr exp))))
(define (named-let-name exp) (cadr exp))
(define (named-let-variables exp) (map car (caddr exp)))
(define (named-let-values exp) (map cadr (caddr exp)))
(define (named-let-body exp) (cadddr exp))
                      
(define (named-let->func exp)
  (list 'define 
        (cons (named-let-name exp)
              (named-let-variables exp))
        (named-let-body exp)))

(define (let->combination exp)
  (if (named-let? exp)
      (sequence->exp (list (named-let->func exp)
                           (cons (named-let-name exp)
                                 (named-let-values exp))))
      (cons (make-lambda (let-variables exp) 
                         (let-body exp))
            (let-values exp))))


  
;while  
(define (while? exp) (tagged-list? exp 'while)) 
(define (while-condition exp) (cadr exp)) 
(define (while-body exp) (caddr exp)) 
(define (while->combination exp)
  (sequence->exp (list (list 'define  
                             (list 'while-iter) 
                             (make-if 
                              (while-condition exp)        
                              (sequence->exp (list 
                                              (while-body exp)
                                              (list 'while-iter))) 
                                      'true)) 
                       (list 'while-iter))))

;map
(define (map? exp) (tagged-list? exp 'map))
(define (map-proc exp) (cadr exp))
(define (map-items exp) (caddr exp))
(define (map->combination exp)
  (sequence->exp
   (list (list 'define
               (list 'mmap 'proc 'items)
               (make-if 
                (list 'null? 'items)
                ''()
                (list 'cons
                      (list 'proc
                            (list 'car 'items))
                      (list 'mmap 'proc 
                                 (list 'cdr 'items)))))
         (list 'mmap (map-proc exp) (map-items exp)))))

;run
(define the-global-environment (setup-environment))
(driver-loop)

  
