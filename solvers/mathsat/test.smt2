(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)

; 第一个上下文
(push 1)   ; 注意这里加了数字1
(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ x y) 10))

; 优化目标：最大化x
(maximize x)
(check-sat)
(get-model)
(get-objectives)

; 弹出并添加新的约束
(pop 1)    ; 注意这里加了数字1
(push 1)   ; 注意这里加了数字1
(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ x y) 10))
(assert (>= y 5))

; 新的优化目标：最小化x+y
(minimize (+ x y))
(check-sat)
(get-model)
(get-objectives)
(pop 1)    ; 注意这里加了数字1