REBOL []

cs: func [x] [
	(cosine/radians x) - (x * x * x)
]

fn: func [x] [
	power (x - 1) 3
]

math: context [
	; Tolerance
	eps:       1E-15
	; Maximum number of steps for iterative methods
	max-steps: 100
	; Current number of steps
	steps:     0
	
	; Numerical differentiation
	; Methods:
	;  simple: differentiation by definition
	;  five-point: five-point stencil
	derive: context [
		tr: 0
		simple: func [
			f [function!]
			x [decimal!]
		] [
			((f x + eps) - (f x)) / eps
		]
		five-point: func [
			f [function!]
			x [decimal!]
			/local d1 d2 d3 d4
		] [
			d1: negate f x + (2 * eps)
			d2: 8 * (f x + eps)
			d3: -8 * (f x - eps)
			d4: f x - (2 * eps)
			(d1 + d2 + d3 + d4) / (12 * eps)
		]
	]

	; Root finding methods
	; Solve the equation f(x) = 0
	; Root bracketing methods:
	; Take three arguments: function, left border and right border
	; Methods:
	;  bisection: Bisection method
	;  false-position: False position method
	;  illinois: Illinois variation of false position method
	;  ridders: Ridder's method
	;  brent: Brent method
	; Newton-based methods:
	; Take two arguments: function and initial guess
	; Optinal argument /derive: differentiation procedure
	; Methods:
	;  newton
	roots: context [
		bisection: func [
			f [function!]
			a [decimal!]
			b [decimal!]
			/local fa fb fc c
		] [
			steps: 1
			fa: f a
			fb: f b
			if (sign? fa) = (sign? fb) [
				return "points do not straddle"
			]
			while [steps < max-steps] [
				c:  (a + b) / 2
				fc: f c
				if ((abs fc) < eps) or (b - a < eps) [
					return c
				]
				either (sign? fc) = (sign? fa) [
					a:  c
					fa: fc
				] [
					b:  c
					fb: fc
				]
				steps: steps + 1
			]
			"maximum number of steps exceeded"
		]

		false-position: func [
			f [function!]
			a [decimal!]
			b [decimal!]
			/local fa fb fc c side
		] [
			steps: 1
			side:  0
			fa:    f a
			fb:    f b
			if (sign? fa) = (sign? fb) [
				return "points do not straddle"
			]
			while [steps < max-steps] [
				c:  b - (fb * (b - a) / (fb - fa))
				fc: f c
				if ((abs fc) < eps) or (b - a < eps) [
					return c
				]
				either (sign? fc) = (sign? fa) [
					a:  c
					fa: fc
					if side = 1 [ fb: fb / 2 ]
					side: 1
				] [
					b:  c
					fb: fc
					if side = -1 [ fa: fa / 2 ]
					side: -1
				]
				steps: steps + 1
			]
			"maximum number of steps exceeded"
		]

		illinois: func [
			f [function!]
			a [decimal!]
			b [decimal!]
			/local fa fb fc c side
		] [
			steps: 1
			side:  0
			fa: f a
			fb: f b
			if (sign? fa) = (sign? fb) [
				return "points do not straddle"
			]	
			while [steps < max-steps] [
				c:  ((0.5 * fb * a) - (fa * b)) / ((0.5 * fb) - fa)
				fc: f c
				if ((abs fc) < eps) or (b - a < eps) [
					return c
				]
				either (sign? fc) = (sign? fa) [
					a: c
					fa: fc
					if side = 1 [ fb: fb / 2 ]
					side: 1
				] [
					b: c
					fb: fc
					if side = -1 [ fa: fa / 2 ]
					side: -1
				]
				steps: steps + 1
			]
			"maximum number of steps exceeded"
		]

		ridders: func [
			f [function!]
			a [decimal!]
			b [decimal!]
			/local fa fb fc fd c d
			qtt mdl
		] [
			steps: 1
			fa:  f a
			fb:  f b
			if (sign? fa) = (sign? fb) [
				return "points do not straddle"
			]
			while [steps < max-steps] [
				c:   (a + b) / 2
				fc:  f c
				qtt: (sign? fa - fb) * fc
				mdl: square-root fc * fc - (fa * fb)
				d:   c + ((c - a) * qtt / mdl)
				fd:  f d
				if ((abs fd) < eps) or ((b - a) / 2 < eps) [
					return d
				]
				either (sign? fd) = (sign? fa) [
					a:  d
					fa: fd
				] [
					b:  d
					fb: fd
				]
				steps: steps + 1
			]
			"maximum number of steps exceeded"
		]

		brent: func [
			f [function!]
			a [decimal!]
			b [decimal!]
			/local fa fb fc fs c d s mflag
			s1 s2 s3 t
			cond1 cond2 cond3 cond4 cond5
		] [
			steps: 1
			fa:    f a
			fb:    f b
			if (sign? fa) = (sign? fb) [
				return "points do not straddle"
			]
			c:     a
			fc:    fa
			mflag: true
			while [steps < max-steps] [
				either (fc != fa) and (fb != fc) [
					s1: (a * fb * fc) / ((fa - fb) * (fa - fc))
					s2: (b * fa * fc) / ((fb - fa) * (fb - fc))
					s3: (c * fa * fb) / ((fc - fa) * (fc - fb))
					s:  s1 + s2 + s3
				] [
					s:  b - (fb * (b - a) / (fb - fa))
				]
				cond1: (s < ((3 * a + b) / 4)) or (s > b)
				cond2: either mflag [
					(abs s - b) >= ((b - c) / 2)
				] [false]
				cond3: either not mflag [
					(abs s - b) >= ((c - d) / 2)
				] [false]
				cond4: either mflag [
					(abs b - c) < eps
				] [false]
				cond5: either not mflag [
					(abs c - d) < eps
				] [false]
				either cond1 or cond2 or cond3 or cond4 or cond5 [
					s:     (a + b) / 2
					mflag: true
				] [mflag: false]
				fs: f s
				d:  c
				c:  b
				fc: fb
				either (sign? fa) != (sign? fs) [
					b:  s
					fb: fs
				] [
					a:  s
					fa: fs
				]
				if (abs fa) < (abs fb) [
					t:  b
					b:  a
					a:  t
					t:  fb
					fb: fa
					fa: t
				]
				cond1: (abs fb) < eps
				cond2: (abs fs) < eps
				cond3: (abs b - a) < eps
				if cond1 or cond2 or cond3 [ return b ]
				steps: steps + 1
			]
			"maximum number of steps exceeded"
		]

		newton: func [
			f  [function!]
			x  [decimal!]
			/diff
			df [function!]
			/local fx dfx
		] [
			steps: 1
			while [steps < max-steps] [
				fx:  f x
				if (abs fx) < eps [ return x ]
				dfx: either diff [df :f x] [derive/five-point :f x]
				x:   x - (fx / dfx)
				steps: steps + 1				
			]
			"maximum number of steps exceeded"
		]

		steffensen: func [
			f [function!]
			x [decimal!]
			/local fx gx x1 x2
		] [
			steps: 1
			while [steps < max-steps] [
				fx: f x
				if (abs fx) < eps [ return x ]
				gx: ((f x + fx) - fx) / fx
				x:  x - (fx / gx)
				steps: steps + 1
			]
			"maximum number of steps exceeded"
		]

		steffensen-aitken: func [
			f [function!]
			x [decimal!]
			/local fx ffx u v
		] [
			steps: 1
			while [steps < max-steps] [
				fx:  f x
				if (abs f x) < eps [ return x ]
				ffx: f fx
				u:   power (fx - x) 2
				v:   ffx - (2 * fx) + x 
				x:   x - (u / v)
				print u 
				steps: steps + 1
			]
			"maximum number of steps exceeded"
		]
	]
]