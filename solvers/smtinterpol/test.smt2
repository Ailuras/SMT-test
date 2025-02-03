(set-logic QF_LIA)  ; 设置逻辑为线性整数算术
(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)

; 第一个上下文
(push 1)
(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ x y) 10))

; SMTInterpol不直接支持maximize/minimize
; 我们可以通过断言和检查来模拟
(check-sat)
(get-model)

; 弹出并添加新的约束
(pop 1)
(push 1)
(assert (>= x 0))
(assert (>= y 0))
(assert (<= (+ x y) 10))
(assert (>= y 5))

(check-sat)
(get-model)
(pop 1)