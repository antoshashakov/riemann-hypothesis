import Lib.General.NumberTheory.ImaginaryQuadraticField

/-!
# Quadratic twists, polar functions and logarithmic derivatives of Dirichlet L-functions

This part shows that the twist of a Dirichlet character by the Legendre symbol of an odd prime not
dividing the modulus is not principal. It defines `New.IsPolar`, the condition that a Laplace-type
transform of an error term continues meromorphically with at most simple poles in the right
half-plane. It also expresses `∑ χ(n) Λ(n) n^{-s}` through the logarithmic derivative of
`New.entireL χ` and identifies the residues of that logarithmic derivative with the orders of the
zeros of `New.entireL χ`.

## Main definitions and results

* `New.quadTwist_ne_one`: the twist of a character modulo `N` by the Legendre symbol `(·/d)`, for an
  odd prime `d` prime to `N`, is not principal.
* `New.IsPolar`: `E` is measurable, `|E v| ≤ C e^v` for `v ≥ 0`, and `∫₀^∞ E(v) e^{(1-s)v} dv`
  continues to a meromorphic function of `s` with at most simple poles of residue `r ρ` in
  `re ρ > 0`.
* `New.LSeriesHasSum_mul_vonMangoldt`: `∑ χ(n) Λ(n) n^{-s}` in terms of the logarithmic derivative
  of `New.entireL χ`.
* `New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt`: the residues of that logarithmic
  derivative are the orders of the zeros of `New.entireL χ`.

Notions from other files:
* `New.entireL`: The entire function equal to L(s, χ) if χ is not principal, and to the continuation
  of (s − 1)L(s, χ) if χ is principal.

## Relation to the literature

Known; see `Lib.Analytic.Landau` for sources.
-/

open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory Metric ProbabilityTheory
  Nat Topology ComplexOrder AnalyticOnNhd Real

namespace New

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]

/-! ### The quadratic twist of a character -/

/-- The twist of `χ` by the Legendre symbol takes the value `χ(n) (n/d)` at an integer `n`. -/
lemma quadTwist_apply (n : ℤ) : quadTwist χ d n = χ n * legendreSym d n :=
  show _ = _ * (chiK d).ringHomComp (algebraMap ..) n by  grind [quadTwist, MulChar.mul_apply,
  changeLevel_eq_cast_of_dvd', apply_eq_zero_iff, IsCoprime.mul_right]

/-- For a Dirichlet character `χ` mod `N` and an odd prime `d` coprime to `N`, the twist of `χ` by
the Legendre symbol `(·/d)`, a character mod `N * d`, is not principal. -/
lemma quadTwist_ne_one (hd : d ≠ 2) (hN : N.Coprime d) : quadTwist χ d ≠ 1 :=
  (quadraticChar_exists_neg_one (ZMod.ringChar_zmod_n d ▸ hd)).elim fun a _ e ↦
    (chineseRemainder hN 1 a.val).rec fun n _ ↦ by
      obtain := quadTwist_apply χ d n, (quadTwist χ d).mul_apply 1 n
      simp_all [legendreSym, ← ZMod.natCast_eq_natCast_iff, neg_eq_self]

/-! ### Polar functions and Laplace integrals -/

/-- `E` is measurable, `|E v| ≤ C e^v` for all `v ≥ 0`, and its transform
`∫₀^∞ E(v) e^{(1-s)v} dv` continues from `re s > 2` to a meromorphic function on `ℂ` whose poles in
`re s > 0` are at most simple; for `re ρ > 0`, `r ρ` is the residue at `ρ`, and `0` where there is
no pole. For `E(v) = R(e^v)` the transform is `∫₁^∞ R(y) y^{-s} dy`. -/
def IsPolar (E : ℝ → ℝ) (r : ℂ → ℂ) : Prop :=
  Measurable E ∧
  ∃ (C : ℝ) (Φ : ℂ → ℂ),
    Meromorphic Φ ∧
    -- (a) exponential growth
    (∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) ∧
    -- (b) `Φ` is the transform of `E` far to the right
    (∀ s : ℂ, 2 < re s → Φ s = ∫ v : ℝ in Ioi 0, E v * Complex.exp ((1 - s) * v)) ∧
    -- (c) at most simple poles in `re ρ > 0`, with residues `r ρ`
    ∀ ρ : ℂ, 0 < re ρ → Tendsto (fun z ↦ (z - ρ) * Φ z) (𝓝[≠] ρ) (𝓝 (r ρ))

variable {E : ℝ → ℝ} [NeZero N] {s : ℂ}

/-- If `E` is measurable and `|E v| ≤ C e^v` for `v ≥ 0`, the transform
`∫₀^∞ E(v) e^{(1-s)v} dv` converges for `re s > 2`. -/
lemma integrableOn_laplace_of_abs_le {C : ℝ} (hE : Measurable E)
    (hE_growth : ∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) (hs : 2 < s.re) :
    IntegrableOn (fun v : ℝ ↦ E v * Complex.exp ((1 - s) * v)) (Ioi 0) :=
  ((integrableOn_exp_mul_Ioi (sub_neg.2 hs) 0).const_mul C).mono' (by fun_prop)
    (ae_restrict_of_forall_mem (by simp) (by
      simp_intro ..
      simp only [norm_exp, mul_re, sub_re, one_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      grw [hE_growth, mul_assoc, ← Real.exp_add] <;> grind))

/-- For `re s > 0`, the Laplace transform of `t ^ k` at `s` is `k! / s ^ (k + 1)`. -/
lemma laplace_pow {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ∫ t : ℝ in Ioi 0, t ^ k * Complex.exp (-s * t) = k ! / s ^ (k + 1) := by
  have h : (-s).re < 0 := by simpa using hs
  exact (iteratedDeriv_complexMGF
    (interior_maximal (@integrableOn_exp_mul_Ioi · · 0) isOpen_Iio h) _ ▸
    EqOn.iteratedDeriv_of_isOpen (@integral_exp_mul_complex_Ioi · · 0)
      (isOpen_re_lt 0) k h).trans (by
    simp [neg_div, iteratedDeriv_eq_iterate, zpow_sub₀ (h.ne ∘ congr rfl), neg_pow s, pow_succ,
      field])

/-! ### The logarithmic derivative of a Dirichlet L-function -/

@[fun_prop]
lemma analyticAt_entireL (s : ℂ) : AnalyticAt ℂ (entireL χ) s :=
  Differentiable.analyticAt (by
    grind [entireL, differentiable_LFunctionTrivChar₁, differentiable_LFunction]) s

/-- `entireL χ` has no zero in `re s ≥ 1`. -/
lemma entireL_ne_zero (hs : 1 ≤ s.re) : entireL χ s ≠ 0 := by
  rw [entireL]; grind [LFunction_ne_zero_of_one_le_re, LFunctionTrivChar₁_apply_one_ne_zero]

/-- For `re s > 1`, the series `∑ χ(n) Λ(n) n^{-s}` has the sum `-L'/L(s, χ)`, written through
`entireL χ`, which is `L(s, χ)`, or `(s - 1) L(s, χ)` for principal `χ`. The term `1 / (s - 1)` is
present only for `χ = 1`. -/
lemma LSeriesHasSum_mul_vonMangoldt (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ χ n * Λ n) s
      ((if χ = 1 then 1 else 0) / (s - 1) - logDeriv (entireL χ) s) :=
  LSeriesHasSum_iff.2 ⟨χ.LSeriesSummable_twist_vonMangoldt hs, by
    erw [entireL, logDeriv_apply, LSeries_twist_vonMangoldt_eq] <;>
      grind [LFunction_ne_zero_of_one_le_re, one_re, deriv_LFunctionTrivChar₁_apply_of_ne_one,
        LFunction_eq_LSeries, deriv_LFunction_eq_deriv_LSeries]⟩

/-- A function continuous at `s` has residue zero there. -/
lemma tendsto_sub_mul_of_continuousAt {f : ℂ → ℂ} (hf : ContinuousAt f s) :
    Tendsto (fun z : ℂ ↦ (z - s) * f z) (𝓝[≠] s) (𝓝 0) := by
  simpa using ((tendsto_id.sub_const s).mul hf).mono_left nhdsWithin_le_nhds

lemma analyticOrderAt_entireL_ne_top (s : ℂ) : analyticOrderAt (entireL χ) s ≠ ⊤ := by
  -- An entire function of infinite order at a point is zero, but `entireL χ 1 ≠ 0`.
  exact fun h_top ↦ entireL_ne_zero χ le_rfl
    (congrFun ((analyticOrderAt_eq_top_iff_eq_zero s (by fun_prop)).1 h_top) 1)

lemma analyticOrderNatAt_entireL_eq_zero_iff (s : ℂ) :
    analyticOrderNatAt (entireL χ) s = 0 ↔ entireL χ s ≠ 0 := by
  rw [← (analyticAt_entireL χ s).analyticOrderAt_eq_zero,
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_entireL_ne_top χ s), Nat.cast_eq_zero]

/-- The logarithmic derivative of `entireL χ`, which is `L(s, χ)`, or `(s - 1) L(s, χ)` for
principal `χ`, has at most a simple pole at `s`. Its residue is the order of vanishing of
`entireL χ` at `s`. -/
lemma tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt (s : ℂ) :
    Tendsto (fun z : ℂ ↦ (z - s) * logDeriv (entireL χ) z) (𝓝[≠] s)
      (𝓝 (analyticOrderNatAt (entireL χ) s : ℂ)) := by
  obtain ⟨g, a, b, e⟩ := (analyticAt_entireL χ s).analyticOrderAt_ne_top.1
    (analyticOrderAt_entireL_ne_top χ s)
  have hlim : Tendsto (fun z : ℂ ↦ (analyticOrderNatAt (entireL χ) s : ℂ) +
      (z - s) * logDeriv g z) (𝓝[≠] s) (𝓝 (analyticOrderNatAt (entireL χ) s : ℂ)) := by
    simpa [logDeriv_apply] using
      (tendsto_sub_mul_of_continuousAt (a.deriv.div a b).continuousAt).const_add
      (analyticOrderNatAt (entireL χ) s : ℂ)
  refine hlim.congr' ?_
  exact mem_inf_principal.2 (by
    filter_upwards [e.deriv, e, a.continuousAt.eventually_ne b, a.eventually_analyticAt]
    cases analyticOrderNatAt (entireL χ) s <;>
      simp +contextual (disch := fun_prop) [logDeriv, field]
    grind)

end New
