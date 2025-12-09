(assert
	(forall
		((|n:36| Int) (|1.n:0| Int) (|1.n:1| Int) (|1.n:2| Int) (|1.n:3| Int))
		(=>
			(or
				(and
					(= |n:36| 1)
					(= |1.n:3| (+ |1.n:2| 1))
					(= (< |1.n:2| 0) false)
					(= (> |1.n:1| 0) false)
					(= |1.n:0| 10))
				(and
					(= |n:36| 1)
					(= |1.n:3| (- 0 |1.n:2|))
					(< |1.n:2| 0)
					(= (> |1.n:1| 0) false)
					(= |1.n:0| 10)))	
			(< |1.n:3| 0)
		)
	)
)

; check should fail, because |1.n:3| is never smaller 0
(check-sat)
