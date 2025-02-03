(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)

; 第一个上下文
(push)
(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ x y) 10))

; 在这个上下文中优化x的值（最大化）
(maximize x)
(check-sat)
(get-model)
(get-objectives)

; 弹出并添加新的约束
(pop)
(push)
(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ x y) 10))
(assert (>= y 5))

; 尝试新的优化目标（最小化x+y）
(minimize (+ x y))
(check-sat)
(get-model)
(get-objectives)
(pop)