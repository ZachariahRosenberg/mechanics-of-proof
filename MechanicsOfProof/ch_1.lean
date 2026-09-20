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
example
