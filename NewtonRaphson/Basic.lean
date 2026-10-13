import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# the definitions

`newtonStep` is one step, `newtonSeq` just keeps doing it, and `LocalNewtonHypotheses` is
everything i need to know about `f` near the root, in one place.

the hypotheses are the normal ones from any numerics course, except that every constant
is written down. a root `r`, a radius `ρ`, `|f'| ≥ m` and `|f''| ≤ M` on the ball around
`r`, and `M * ρ < 2 * m`. careful, this is the local theorem where the root is already
known. the real kantorovich theorem starts from `x₀` alone and proves there is a root at
all, that one is still on my list.
-/

noncomputable section

/-- One Newton step, `x - f x / f' x`. in lean `a / 0 = 0`, so where `f' x = 0` this just
gives back `x`. meaningless, but the hypotheses never let us get there anyway. -/
def newtonStep (f f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  x - f x / f' x

/-- The Newton iterates `x₀, N x₀, N (N x₀), ...` -/
def newtonSeq (f f' : ℝ → ℝ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => newtonStep f f' (newtonSeq f f' x₀ n)

@[simp] lemma newtonSeq_zero (f f' : ℝ → ℝ) (x₀ : ℝ) : newtonSeq f f' x₀ 0 = x₀ := rfl

@[simp] lemma newtonSeq_succ (f f' : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    newtonSeq f f' x₀ (n + 1) = newtonStep f f' (newtonSeq f f' x₀ n) := rfl

/-- What we assume about `f` on the closed ball `|x - r| ≤ ρ`.

i pass `f'` and `f''` in as functions with `HasDerivAt` facts instead of using `deriv`.
that way the √2 example just hands over `fun x => 2 * x` and nothing ever has to
compute a derivative. -/
structure LocalNewtonHypotheses (f f' f'' : ℝ → ℝ) (r ρ m M : ℝ) : Prop where
  root : f r = 0
  radius_pos : 0 < ρ
  m_pos : 0 < m
  M_nonneg : 0 ≤ M
  deriv_f : ∀ x, |x - r| ≤ ρ → HasDerivAt f (f' x) x
  deriv_f' : ∀ x, |x - r| ≤ ρ → HasDerivAt f' (f'' x) x
  /-- `|f'|` stays away from zero, the sign does not matter -/
  deriv_lower : ∀ x, |x - r| ≤ ρ → m ≤ |f' x|
  second_bound : ∀ x, |x - r| ≤ ρ → |f'' x| ≤ M
  /-- the whole proof hangs on this one, see `rate_lt_one` -/
  contraction : M * ρ < 2 * m

namespace LocalNewtonHypotheses

variable {f f' f'' : ℝ → ℝ} {r ρ m M : ℝ}

lemma deriv_ne_zero (H : LocalNewtonHypotheses f f' f'' r ρ m M) (x : ℝ) (hx : |x - r| ≤ ρ) :
    f' x ≠ 0 := by
  intro h
  have := H.deriv_lower x hx
  rw [h, abs_zero] at this
  linarith [H.m_pos]

lemma const_nonneg (H : LocalNewtonHypotheses f f' f'' r ρ m M) : 0 ≤ M / (2 * m) :=
  div_nonneg H.M_nonneg (by linarith [H.m_pos])

/-! `M / (2 * m) * ρ` is how much one step shrinks the error at worst while we are inside
the ball. Everything else is about showing it is below one. -/

lemma rate_nonneg (H : LocalNewtonHypotheses f f' f'' r ρ m M) : 0 ≤ M / (2 * m) * ρ :=
  mul_nonneg H.const_nonneg H.radius_pos.le

lemma rate_lt_one (H : LocalNewtonHypotheses f f' f'' r ρ m M) : M / (2 * m) * ρ < 1 := by
  have hm : 0 < 2 * m := by linarith [H.m_pos]
  rw [div_mul_eq_mul_div, div_lt_one hm]
  exact H.contraction

end LocalNewtonHypotheses
