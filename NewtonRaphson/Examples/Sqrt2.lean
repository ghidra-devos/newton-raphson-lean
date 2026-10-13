import NewtonRaphson.Convergence

/-!
# example, √2

newton on `x ^ 2 - 2` from `3/2`. for this `f` the step is the average of `x` and `2 / x`,
the babylonians already did it this way.

constants `r = √2`, `ρ = 1/2`, `m = 1`, `M = 2`. in the ball every `x` is above
`√2 - 1/2 > 1/2`, so `|f' x| = 2x > 1`, and `f''` is just 2. `M * ρ = 1 < 2 = 2 * m`.
`C` comes out exactly 1, so the general theorem says `|xₙ - √2| ≤ |x₀ - √2| ^ (2 ^ n)`.

what you feed in as `|x₀ - √2|` matters a lot. my first version used `1/2` and got
`1/4, 1/16, 1/256`, true but it makes newton look slow. `3/2` is within `1/10` of `√2`
and then it is `10⁻², 10⁻⁴, 10⁻⁸`, which is what really happens.
-/

noncomputable section

namespace Sqrt2

open Filter Topology

def f : ℝ → ℝ := fun x => x ^ 2 - 2
def f' : ℝ → ℝ := fun x => 2 * x
def f'' : ℝ → ℝ := fun _ => 2

lemma hasDerivAt_f (x : ℝ) : HasDerivAt f (f' x) x := by
  have h : HasDerivAt (fun y : ℝ => y ^ 2 - 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const 2
  exact h

lemma hasDerivAt_f' (x : ℝ) : HasDerivAt f' (f'' x) x := by
  have h : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  exact h

-- √2 squared is 2 and √2 is not negative, nlinarith gets every bound below from these two
lemma sqrt_two_sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma seven_fifths_le_sqrt_two : 7 / 5 ≤ √2 := by
  nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]

lemma sqrt_two_le_three_halves : √2 ≤ 3 / 2 := by
  nlinarith [sqrt_two_sq, Real.sqrt_nonneg 2]

lemma f'_lower (x : ℝ) (hx : |x - √2| ≤ 1 / 2) : 1 ≤ |f' x| := by
  have h := (abs_le.mp hx).1
  have := seven_fifths_le_sqrt_two
  rw [f', abs_of_pos (by linarith)]
  linarith

theorem hypotheses : LocalNewtonHypotheses f f' f'' √2 (1 / 2) 1 2 where
  root := by simp [f]
  radius_pos := by norm_num
  m_pos := by norm_num
  M_nonneg := by norm_num
  deriv_f := fun x _ => hasDerivAt_f x
  deriv_f' := fun x _ => hasDerivAt_f' x
  deriv_lower := f'_lower
  second_bound := fun x _ => by simp [f'']
  contraction := by norm_num

def x₀ : ℝ := 3 / 2

/-- `3/2` is within a tenth of `√2`, from `1.4 ≤ √2 ≤ 1.5`. -/
lemma x₀_close : |x₀ - √2| ≤ 1 / 10 := by
  have h1 := seven_fifths_le_sqrt_two
  have h2 := sqrt_two_le_three_halves
  rw [x₀, abs_le]
  constructor <;> linarith

lemma x₀_in_ball : |x₀ - √2| ≤ 1 / 2 := x₀_close.trans (by norm_num)

def seq : ℕ → ℝ := newtonSeq f f' x₀

/-! The first iterates as exact fractions. Numerator and denominator roughly square each
time, 577/408 is about 1.4142157 and 665857/470832 already agrees with √2 to 12 places. -/

lemma seq_one : seq 1 = 17 / 12 := by
  norm_num [seq, newtonStep, x₀, f, f']

lemma seq_two : seq 2 = 577 / 408 := by
  rw [seq, newtonSeq_succ, ← seq, seq_one]
  norm_num [newtonStep, f, f']

lemma seq_three : seq 3 = 665857 / 470832 := by
  rw [seq, newtonSeq_succ, ← seq, seq_two]
  norm_num [newtonStep, f, f']

theorem converges : Tendsto seq atTop (𝓝 √2) :=
  hypotheses.newton_converges x₀_in_ball

theorem stays_in_ball (n : ℕ) : |seq n - √2| ≤ 1 / 2 :=
  hypotheses.newton_stays_in_ball x₀_in_ball n

/-- With `C = 1` the quadratic bound is just "the error squares". -/
theorem error_squares (n : ℕ) : |seq (n + 1) - √2| ≤ |seq n - √2| ^ 2 := by
  have h := hypotheses.newton_quadratic_rate x₀_in_ball n
  norm_num at h
  simpa [seq, sq_abs] using h

/-- The error after `n` steps is at most `10 ^ (-2 ^ n)`. -/
theorem error_bound (n : ℕ) : |seq n - √2| ≤ (1 / 10) ^ (2 ^ n) := by
  have h := hypotheses.newton_doubly_exponential x₀_in_ball n
  norm_num at h
  exact h.trans (pow_le_pow_left₀ (abs_nonneg _) (by simpa using x₀_close) _)

example : |seq 1 - √2| ≤ 1 / 100 := by
  have h := error_bound 1
  norm_num at h ⊢
  exact h

example : |seq 2 - √2| ≤ 1 / 10 ^ 4 := by
  have h := error_bound 2
  norm_num at h ⊢
  exact h

example : |seq 3 - √2| ≤ 1 / 10 ^ 8 := by
  have h := error_bound 3
  norm_num at h ⊢
  exact h

end Sqrt2
