import NewtonRaphson.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# one step, how far from the root does it land

this whole file is for one inequality,

  |N x - r| ≤ M / (2 * m) * |x - r| ^ 2

first the exact formula for `N x - r`, then a bound on the taylor remainder inside it.

the remainder is the only real analysis in the project and the part that took the
longest. taylor with the lagrange remainder would do it in one line on paper, but
mathlib's version wants `iteratedDerivWithin` and `ContDiffOn` and i only have
`HasDerivAt`. so i went around it with cauchy's mean value theorem and two functions
picked for it, see `taylor_remainder_bound`.
-/

namespace LocalNewtonHypotheses

open Set

variable {f f' f'' : ℝ → ℝ} {r ρ m M : ℝ}

/-- Pure algebra, only needs `f' x ≠ 0`. -/
lemma step_error_identity (H : LocalNewtonHypotheses f f' f'' r ρ m M) (x : ℝ)
    (hx : |x - r| ≤ ρ) :
    newtonStep f f' x - r = -(f x - f' x * (x - r)) / f' x := by
  have h := H.deriv_ne_zero x hx
  unfold newtonStep
  field_simp
  ring

/-- `|f x - f' x * (x - r)| ≤ M / 2 * |x - r| ^ 2`, the remainder of the tangent line at
`x`, measured at the root.

Take `φ t = f t + f' t * (r - t)`, the tangent line at `t` evaluated at `r`. Then
`φ r = f r = 0`, `φ x` is the thing we want to bound, and the `f'` terms cancel in the
derivative, `φ' t = f'' t * (r - t)`. Cauchy's mean value theorem against
`ψ t = (t - r) ^ 2` gives a `c` between `x` and `r` with `2 * φ x = -(x - r) ^ 2 * f'' c`,
and `|f'' c| ≤ M` finishes it. on paper this is five lines, in lean the five lines are the
easy part and getting `c` into the ball is the rest. -/
lemma taylor_remainder_bound (H : LocalNewtonHypotheses f f' f'' r ρ m M) (x : ℝ)
    (hx : |x - r| ≤ ρ) :
    |f x - f' x * (x - r)| ≤ M / 2 * |x - r| ^ 2 := by
  set φ : ℝ → ℝ := fun t => f t + f' t * (r - t) with hφ_def
  set ψ : ℝ → ℝ := fun t => (t - r) ^ 2 with hψ_def
  have hφ : ∀ t, |t - r| ≤ ρ → HasDerivAt φ (f'' t * (r - t)) t := by
    intro t ht
    have h := (H.deriv_f t ht).add ((H.deriv_f' t ht).mul ((hasDerivAt_id t).const_sub r))
    convert h using 1
    · funext s
      simp [hφ_def]
    · simp only [id]
      ring
  have hψ : ∀ t, HasDerivAt ψ (2 * (t - r)) t := by
    intro t
    have h := ((hasDerivAt_id t).sub_const r).pow 2
    convert h using 1
    · funext s
      simp [hψ_def]
    · simp
  have hφr : φ r = 0 := by simp [hφ_def, H.root]
  -- every point between x and r is still in the ball
  have between : ∀ t, min x r ≤ t → t ≤ max x r → |t - r| ≤ ρ := by
    intro t h1 h2
    have := abs_le.mp hx
    rw [abs_le]
    constructor
    · cases le_total x r with
      | inl h => rw [min_eq_left h] at h1; linarith
      | inr h => rw [min_eq_right h] at h1; linarith [H.radius_pos]
    · cases le_total x r with
      | inl h => rw [max_eq_right h] at h2; linarith [H.radius_pos]
      | inr h => rw [max_eq_left h] at h2; linarith
  have cont : ∀ a b, min x r ≤ a → b ≤ max x r → ContinuousOn φ (Icc a b) := by
    intro a b ha hb t ht
    exact (hφ t (between t (le_trans ha ht.1) (le_trans ht.2 hb))).continuousAt.continuousWithinAt
  have cont_ψ : ∀ a b, ContinuousOn ψ (Icc a b) := fun a b t _ =>
    (hψ t).continuousAt.continuousWithinAt
  -- the mean value point, the same identity comes out of both orders
  obtain ⟨c, hc, key⟩ : ∃ c, |c - r| ≤ ρ ∧ φ x * 2 = -(x - r) ^ 2 * f'' c := by
    rcases lt_trichotomy x r with hlt | heq | hgt
    · obtain ⟨c, hc, h⟩ := exists_ratio_hasDerivAt_eq_ratio_slope φ (fun t => f'' t * (r - t)) hlt
        (cont x r (min_le_left x r) (le_max_right x r))
        (fun t ht => hφ t (between t (by simp [hlt.le, ht.1.le]) (by simp [hlt.le, ht.2.le])))
        ψ (fun t => 2 * (t - r)) (cont_ψ x r) (fun t _ => hψ t)
      refine ⟨c, between c (by simp [hlt.le, hc.1.le]) (by simp [hlt.le, hc.2.le]), ?_⟩
      have hcr : c - r ≠ 0 := sub_ne_zero.mpr hc.2.ne
      simp only [hψ_def, hφr] at h
      apply mul_left_cancel₀ hcr
      linear_combination h
    · subst heq
      exact ⟨x, by simp [H.radius_pos.le], by simp [hφr]⟩
    · obtain ⟨c, hc, h⟩ := exists_ratio_hasDerivAt_eq_ratio_slope φ (fun t => f'' t * (r - t)) hgt
        (cont r x (min_le_right x r) (le_max_left x r))
        (fun t ht => hφ t (between t (by simp [hgt.le, ht.1.le]) (by simp [hgt.le, ht.2.le])))
        ψ (fun t => 2 * (t - r)) (cont_ψ r x) (fun t _ => hψ t)
      refine ⟨c, between c (by simp [hgt.le, hc.1.le]) (by simp [hgt.le, hc.2.le]), ?_⟩
      have hcr : c - r ≠ 0 := sub_ne_zero.mpr hc.1.ne'
      simp only [hψ_def, hφr] at h
      apply mul_left_cancel₀ hcr
      linear_combination -h
  have hφx : f x - f' x * (x - r) = φ x := by simp only [hφ_def]; ring
  have hb := H.second_bound c hc
  rw [hφx]
  have hsq : 0 ≤ |x - r| ^ 2 := sq_nonneg _
  have h2 : |φ x| * 2 = |x - r| ^ 2 * |f'' c| := by
    rw [← abs_two, ← abs_mul, key, abs_mul, abs_neg, abs_pow]
  nlinarith [mul_le_mul_of_nonneg_left hb hsq]

/-- One step squares the error, up to the factor `M / (2 * m)`. -/
theorem newton_error_bound (H : LocalNewtonHypotheses f f' f'' r ρ m M) (x : ℝ)
    (hx : |x - r| ≤ ρ) :
    |newtonStep f f' x - r| ≤ M / (2 * m) * |x - r| ^ 2 := by
  have hne := H.deriv_ne_zero x hx
  have hm := H.m_pos
  have hpos : 0 < |f' x| := abs_pos.mpr hne
  rw [H.step_error_identity x hx, abs_div, abs_neg, div_le_iff₀ hpos]
  calc |f x - f' x * (x - r)|
      ≤ M / 2 * |x - r| ^ 2 := H.taylor_remainder_bound x hx
    _ = M / (2 * m) * |x - r| ^ 2 * m := by field_simp
    _ ≤ M / (2 * m) * |x - r| ^ 2 * |f' x| :=
        mul_le_mul_of_nonneg_left (H.deriv_lower x hx)
          (mul_nonneg H.const_nonneg (sq_nonneg _))

/-- At the root the step does nothing. -/
lemma newton_at_root (H : LocalNewtonHypotheses f f' f'' r ρ m M) : newtonStep f f' r = r := by
  simp [newtonStep, H.root]

end LocalNewtonHypotheses
