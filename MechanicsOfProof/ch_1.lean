import mathlib.tactic
set_option linter.style.whitespace false

-- Proving Equalities

-- 1.2.1
-- the "h" in "h1, h2" stands for hypothesis
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a+b)^2 = 20 :=
  calc
    (a + b)^2
      = (a - b)^2 + 4*(a*b) := by ring
    _ = 4^2 + 4*1 := by rw [h1, h2]
    _ = 20 := by ring

-- 1.2.2
example {r s : ℝ} (h1 : r + 2*s = -1) (h2 : s=3) : (r=-7) :=
  calc
    r
      = (r + 2*s) - 2*s := by ring
    _ = (-1 - 2*s) := by rw [h1]
    _ = (-1 - 2*3) := by rw [h2]
    _ = -7 := by ring

--  1.2.3
example {a b m n : ℤ} (h1 : b^2 = 2*a^2) (h2 : a*m + b*n = 1) : (2*a*n + b*m)^2 = 2 :=
  calc
    (2*a*n + b*m)^2
      = 4*a^2*n^2 + 4*a*n*b*m + b^2*m^2 := by ring
    _ = 2*(a^2*m^2 + 2*a*n*b*m + b^2*n^2) + (4*a^2*n^2 + b^2*m^2 - 2*a^2*m^2 - 2*b^2*n^2) := by ring
    _ = 2*(a*m+b*n)^2 + (m^2 - 2*n^2) * (b^2 - 2*a^2) := by ring
    _ = 2 * 1^2 + (m^2 - 2*n^2)*(2*a^2 - 2*a^2) := by rw [h1, h2]
    _ = 2 := by ring

-- 1.2.4
example {a b c d e f : ℤ} (h1: a*d = b*c) (h2: c*f = d*e) : d*(a*f - b*e) = 0 :=
  calc
    d * (a*f - b*e)
      = d*a*f - d*b*e := by ring
    _ = (a*d) * f - (d*e) * b := by ring
    _ = (b*c) * f - (c*f) * b := by rw [h1, h2]
    _ = b*c*f - b*c*f := by ring
    _ = 0 := by ring

-- 1.3.1
example {a b : ℤ} (h1: a = 2*b + 5) (h2: b=3) : a = 11 :=
  calc
    a
      = 2*b + 5 := by rw [h1]
    _ = 2*(3) + 5 := by rw [h2]
    _ = 11 := by ring

-- 1.3.2
example {x : ℤ} (h1: x+4=2) : x = -2 :=
  calc
    x
      = (x+4) - 4 := by ring -- since our hypothesis has x+4 on left side, we add this identity +4-4
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

-- 1.3.3
example {a b : ℝ} (h1: a-5*b=4) (h2: b+2=3) : a=9 :=
  calc
    a
      = (a-5*b) + 5*b := by ring
    _ = 4 + 5*b := by rw [h1]
    _ = 4 + 5*b - 5*(b+2) + 5*(b+2) := by ring
    _ = 4 - ((5*b) - (5*b)+10) + 5 * (b+2) := by ring
    _ = 4 - 10 + 5 * (b+2) := by ring
    _ = 4 - 10 + 5 * (3) := by rw [h2]
    _ = -6 + 15 := by ring
    _ = 9 := by ring

-- 1.3.4
example {w : ℚ} (h1: 3*w+1=4) : w=1 :=
  calc
    w
      = (w + 1) - 1 := by ring
    _ = 3*(w + 1 - 1)/3 := by ring
    _ = 3*(w + 1)/3 - 3*(1/3) := by ring
    _ = (3*w + 3)/3 - 3/3 := by ring
    _ = (3*w + 3 - 2)/3 - (3-2)/3 := by ring
    _ = (3*w + 1)/3 - 1/3 := by ring
    _ = (4)/3 - 1/3 := by rw [h1]
    _ = 1 := by ring

-- 1.3.5
example {x : ℤ} (h1: 2*x+3=x) : x=-3 :=
  calc
    x
      = (2*x+3) - x - 3 := by ring
    _ = (x) - x - 3 := by rw [h1]
    _ = -3 := by ring

-- 1.3.6
example {x y : ℤ} (h1: 2*x-y=4) (h2: y-x+1=2) : x=5 :=
  calc
    x
      = (2*x-y) + (y - x + 1) - 1 := by ring
    _ = (4) + (2) - 1 := by rw [h1, h2]
    _ = 5 := by ring

-- 1.3.7
example {u v : ℚ} (h1: u+2*v=4) (h2: u-2*v=6) : u=5 :=
  calc
    u
      = ((u + 2*v) + (u- 2*v))/2 := by ring
    _ = ((4) + (6))/2 := by rw [h1, h2]
    _ = 5 := by ring

-- 1.3.8
example {x y : ℝ} (h1: x + y=4) (h2: 5*x - 3*y=4) : x=2 :=
  calc
    x
    _ = (8*x)/8 := by ring
    _ = (3*x + 5*x)/8 := by ring
    _ = (3*x + 5*x + 3*y - 3*y)/8 := by ring
    _ = (5*x - 3*y + 3*x + 3*y)/8 := by ring
    _ = ((5*x - 3*y) + 3*(x + y))/8 := by ring
    _ = ((4) + 3*(4))/8 := by rw [h1, h2]
    _ = 2 := by ring

-- Proving Inequalities

-- 1.4.1
example {x y: ℤ} (hx: x + 3<=2) (hy: y + 2 * x >= 3) : y > 3 :=
  calc
    y
    _ = (y + 2 * x) - (2 * x) := by ring
    _ >= 3 - (2 * x) := by rel [hy]
    _ = 9 - 2*(x + 3) := by ring
    _ >= 9 - 2 * 2 := by rel [hx]
    _ > 3 := by norm_num -- textbook uses custom tactic "numbers"

-- 1.4.2
example {s r : ℚ} (hs: s + 3 >= r) (hr: s + r <= 3) : r <= 3 :=
  calc
    r
    _ <= (2 * r + s - s) / 2 := by norm_num
    _ <= (r - s + s + r) / 2 := by norm_num
    _ <= ((s + r) - s + r) / 2 := by norm_num
    _ <= ((3) - s + r) / 2 := by rel [hr]
    _ <= (3 - s + (s + 3)) / 2 := by rel [hs]
    _ = (3 + 3 - s + s) / 2 := by ring
    _ = (6 + s - s) / 2 := by ring
    _ = 6 / 2 := by ring
    _ <= 3 := by norm_num

-- 1.4.3
example {x y : ℤ} (hy: y <= x + 5) (hx: x <= -2) : x + y < 2 :=
  calc
    x + y
    _ = x + y := by ring
    _ <= x + (x+5) := by rel [hy]
    _ <= (-2) + ((-2) + 5) := by rel [hx]
    _ < 2 := by norm_num

-- 1.4.4
example {u v x y A B : ℝ}
  (hA2: A <= 1) (hB: B >= 1)
  (hx: x <= B) (hy: y <= B)
  (hu1: 0 <= u) (hu2: u < A) (hv1: 0 <= v) (hv2: v < A) :
  (u*y) + (v*x) + (u*v) < 3*A*B :=
  calc
    (u*y) + (v*x) + (u*v)
    _ = (u*y) + (v*x) + (u*v) := by ring
    _ <= (u*B) + (v*B) + (u*v) := by rel [hy, hx]
    _ <= (A*B) + (A*B) + (A*v) := by rel [hu2, hv2]
    _ <= (A*B) + (A*B) + (1*v) := by rel [hA2]
    _ <= (A*B) + (A*B) + (B*v) := by rel [hB]
    _ < (A*B) + (A*B) + (B*A) := by rel [hv2]
    _ = 3 * A*B  := by ring

-- 1.4.5
example {t : ℝ} (ht: t >= 10) : t^2 - 3*t + 17 >= 5 :=
  calc
    t^2 - 3*t + 17
    -- direct substitution of t -> 10, 87, doesn't get to >= 5 in proof by calc, counter-intuitively
    --_ = (10)^2 - 3*(10) + 17 := by norm_num
    _ = t * t - 3 * t + 17 := by ring
    _ >= 10*t - 3*t + 17 := by rel [ht]
    _ = 7*t + 17 := by ring
    _ >= 7*(10) + 17 := by rel [ht]
    _ >= 5 := by norm_num

-- 1.4.6
example {n : ℤ} (hn: n >= 5) : n^2 > 2*n + 11 :=
  calc
    n^2
    _ = n*n := by ring
    -- Like 1.4.5, direct sub of n^2 to (5)^2 won't work
    _ >= 5*n := by rel [hn]
    _ = 2*n + 3*n := by ring
    _ >= 2*n + 3*(5) := by rel [hn]
    _ = 2*n + 15 := by ring
    _ > 2*n + 11 := by norm_num

-- 1.4.7
example {m n : ℤ} (h1: m^2 + n <= 2) : n <= 2 :=
  calc
    n
    _ = n := by ring
    _ <= m^2 + n := by nlinarith -- allows for given that squares are necessarily positive
    _ <= 2 := by rel [h1]

-- 1.4.8
example {x y : ℝ} (h1: x^2 + y^2 <= 1) : (x+y)^2 < 3 :=
  calc
    (x+y)^2
    _ <= (x+y)^2 + (x-y)^2 := by nlinarith -- adding the (x-y)^2 must be a non-negative
    _ = x^2 + 2*x*y + y^2 + x^2 -2*x*y + y^2 := by ring
    _ = x^2 + x^2 + y^2 + y^2 + 2*x*y - 2*x*y := by ring
    _ = x^2 + x^2 + y^2 + y^2 := by ring
    _ = 2*(x^2) + 2*(y^2) := by ring
    _ = 2*(x^2 + y^2) := by ring
    _ <= 2*(1) := by rel [h1]
    _ < 3 := by norm_num

-- 1.4.9
example {a b : ℚ} (ha: a > 0) (hb: b > 0) (h1: a+b <= 8) : 3*a*b + a <= 7*b+72 :=
  calc
    3*a*b + a
    _ <=  (3*a*b + a) + 2*b^2 + a^2 := by nlinarith -- I did not come up with 2*b^2+a^2, it's sharp
    _ =  3*a*b + 2*b*b + a*a + a := by ring
    _ =  2*a*b + a*b + 2*b*b + a*a + a := by ring
    _ =  2*a*b + 2*b*b + a*a + a*b + a := by ring
    _ =  2*b*(a+b) + a*(a+b) + a := by ring
    _ <=  2*b*(8) + a*(8) + a := by rel [h1]
    _ =  16*b + 9*a := by ring
    _ =  7*b + 9*b + 9*a := by ring
    _ =  7*b + 9*(a+b) := by ring
    _ <=  7*b + 9*(8) := by rel [h1]
    _ <= 7*b+72 := by norm_num
