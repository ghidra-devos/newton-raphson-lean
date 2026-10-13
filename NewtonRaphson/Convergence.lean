import NewtonRaphson.Taylor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# the iterates stay in the ball and converge

`q = M / (2 * m) * ρ` is below 1, that is `rate_lt_one`. from there

  every iterate stays in the ball, by induction, one step multiplies the error by at most q
  so the error is at most `q ^ n * |x₀ - r|` and goes to zero
  and the quadratic bound holds at every step, which unrolls to
  `C * |xₙ - r| ≤ (C * |x₀ - r|) ^ (2 ^ n)` with `C = M / (2 * m)`

the geometric bound is enough for convergence but it undersells newton completely. the
`2 ^ n` one is what quadratic convergence actually means, the correct digits double.
-/

namespace LocalNewtonHypotheses

open Filter Topology

variable {f f' f'' : ℝ → ℝ} {r ρ m M x₀ : ℝ}

/-- Inside the ball one step shrinks the error by at least the factor `q`. -/
lemma newton_contracts (H : LocalNewtonHypotheses f f' f'' r ρ m M) (x : ℝ)
    (hx : |x - r| ≤ ρ) :
    |newtonStep f f' x - r| ≤ M / (2 * m) * ρ * |x - r| := by
  calc |newtonStep f f' x - r|
      ≤ M / (2 * m) * |x - r| ^ 2 := H.newton_error_bound x hx
    _ = M / (2 * m) * |x - r| * |x - r| := by ring
    _ ≤ M / (2 * m) * ρ * |x - r| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx H.const_nonneg)
          (abs_nonneg _)

lemma newton_next_in_ball (H : LocalNewtonHypotheses f f' f'' r ρ m M) (x : ℝ)
    (hx : |x - r| ≤ ρ) :
    |newtonStep f f' x - r| ≤ ρ :=
  (H.newton_contracts x hx).trans
    ((mul_le_of_le_one_left (abs_nonneg _) H.rate_lt_one.le).trans hx)

theorem newton_stays_in_ball (H : LocalNewtonHypotheses f f' f'' r ρ m M)
    (hx₀ : |x₀ - r| ≤ ρ) (n : ℕ) :
    |newtonSeq f f' x₀ n - r| ≤ ρ := by
  induction n with
  | zero => simpa using hx₀
  | succ n ih => simpa using H.newton_next_in_ball _ ih

theorem newton_error_geometric (H : LocalNewtonHypotheses f f' f'' r ρ m M)
    (hx₀ : |x₀ - r| ≤ ρ) (n : ℕ) :
    |newtonSeq f f' x₀ n - r| ≤ (M / (2 * m) * ρ) ^ n * |x₀ - r| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [newtonSeq_succ, pow_succ']
    calc |newtonStep f f' (newtonSeq f f' x₀ n) - r|
        ≤ M / (2 * m) * ρ * |newtonSeq f f' x₀ n - r| :=
          H.newton_contracts _ (H.newton_stays_in_ball hx₀ n)
      _ ≤ M / (2 * m) * ρ * ((M / (2 * m) * ρ) ^ n * |x₀ - r|) :=
          mul_le_mul_of_nonneg_left ih H.rate_nonneg
      _ = M / (2 * m) * ρ * (M / (2 * m) * ρ) ^ n * |x₀ - r| := by ring

/-- The iterates converge to the root, from anywhere in the ball. -/
theorem newton_converges (H : LocalNewtonHypotheses f f' f'' r ρ m M)
    (hx₀ : |x₀ - r| ≤ ρ) :
    Tendsto (newtonSeq f f' x₀) atTop (𝓝 r) := by
  have hq : Tendsto (fun n : ℕ => (M / (2 * m) * ρ) ^ n * |x₀ - r|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one H.rate_nonneg H.rate_lt_one).mul_const
      |x₀ - r|
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hq
  rw [Real.norm_eq_abs]
  exact H.newton_error_geometric hx₀ n

/-- The quadratic bound, at every step of the sequence. -/
theorem newton_quadratic_rate (H : LocalNewtonHypotheses f f' f'' r ρ m M)
    (hx₀ : |x₀ - r| ≤ ρ) (n : ℕ) :
    |newtonSeq f f' x₀ (n + 1) - r| ≤ M / (2 * m) * |newtonSeq f f' x₀ n - r| ^ 2 := by
  rw [newtonSeq_succ]
  exact H.newton_error_bound _ (H.newton_stays_in_ball hx₀ n)

/-- The quadratic bound unrolled. `e n = C * |xₙ - r|` satisfies `e (n + 1) ≤ e n ^ 2`, so
`e n ≤ e 0 ^ (2 ^ n)`. Once `C * |x₀ - r|` is below `1/10` this is a new correct digit
for every digit you already had. -/
theorem newton_doubly_exponential (H : LocalNewtonHypotheses f f' f'' r ρ m M)
    (hx₀ : |x₀ - r| ≤ ρ) (n : ℕ) :
    M / (2 * m) * |newtonSeq f f' x₀ n - r| ≤ (M / (2 * m) * |x₀ - r|) ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hC := H.const_nonneg
    have he : 0 ≤ M / (2 * m) * |newtonSeq f f' x₀ n - r| := mul_nonneg hC (abs_nonneg _)
    calc M / (2 * m) * |newtonSeq f f' x₀ (n + 1) - r|
        ≤ M / (2 * m) * (M / (2 * m) * |newtonSeq f f' x₀ n - r| ^ 2) :=
          mul_le_mul_of_nonneg_left (H.newton_quadratic_rate hx₀ n) hC
      _ = (M / (2 * m) * |newtonSeq f f' x₀ n - r|) ^ 2 := by ring
      _ ≤ ((M / (2 * m) * |x₀ - r|) ^ (2 ^ n)) ^ 2 := pow_le_pow_left₀ he ih 2
      _ = (M / (2 * m) * |x₀ - r|) ^ (2 ^ (n + 1)) := by rw [← pow_mul, pow_succ]

end LocalNewtonHypotheses
