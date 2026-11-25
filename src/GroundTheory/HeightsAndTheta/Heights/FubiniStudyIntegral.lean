module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set Filter Topology Real

/-- The Euler beta integral at positive integer arguments. -/
private theorem integral_Ioo_pow_mul_one_sub_pow (k b : ℕ) :
    ∫ u in Ioo (0 : ℝ) 1, u ^ k * (1 - u) ^ b =
      ((k.factorial * b.factorial : ℕ) : ℝ) / (k + b + 1).factorial := by
  have hbeta : Complex.betaIntegral (k + 1) (b + 1) =
      ((∫ u in Ioo (0 : ℝ) 1, u ^ k * (1 - u) ^ b : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
    simp only [add_sub_cancel_right, Complex.cpow_natCast, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  apply Complex.ofReal_injective
  rw [← hbeta, Complex.betaIntegral_eq_Gamma_mul_div _ _
    (by simp [Nat.cast_add_one_pos]) (by simp [Nat.cast_add_one_pos])]
  have hsum : (k : ℂ) + 1 + (b + 1) = ((k + b + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  simp only [hsum, Complex.Gamma_nat_eq_factorial, Nat.cast_mul, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_natCast]

theorem integral_Ioi_pow_div_add_pow (c : ℝ) (hc : 0 < c) (k : ℕ) : ∀ b : ℕ,
    IntegrableOn (fun t : ℝ => t ^ b / (c + t) ^ (b + 2 + k)) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), t ^ b / (c + t) ^ (b + 2 + k) =
      ((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1) := by
  intro b
  -- The substitution t = c / u - c sends (0, 1) onto the positive half-line.
  let f (u : ℝ) := c / u - c
  let g (t : ℝ) := t ^ b / (c + t) ^ (b + 2 + k)
  have hderiv (u : ℝ) (hu : u ∈ Ioo 0 1) :
      HasDerivWithinAt f (-(c / u ^ 2)) (Ioo 0 1) u := by
    simpa [f, neg_div] using
      (((hasDerivAt_const u c).fun_div (hasDerivAt_id u) hu.1.ne').sub_const c).hasDerivWithinAt
  have hinj : InjOn f (Ioo 0 1) := by
    intro u _ v _ h
    simpa [f, div_eq_mul_inv, hc.ne'] using h
  have himage : f '' Ioo 0 1 = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact sub_pos.mpr ((lt_div_iff₀ hu.1).mpr (mul_lt_of_lt_one_right hc hu.2))
    · intro ht
      have hct : 0 < c + t := add_pos hc ht
      refine ⟨c / (c + t), ⟨div_pos hc hct,
        (div_lt_one hct).mpr (lt_add_of_pos_right _ ht)⟩, ?_⟩
      simp [f, hc.ne']
  have hweight : EqOn (fun u => |-(c / u ^ 2)| • g (f u))
      (fun u => u ^ k * (1 - u) ^ b / c ^ (k + 1)) (Ioo 0 1) := by
    intro u hu
    have hsub : c / u - c = c / u * (1 - u) := by field_simp [hu.1.ne']
    dsimp only [f, g, smul_eq_mul]
    rw [add_sub_cancel, hsub, abs_neg, abs_of_pos (div_pos hc (sq_pos_of_pos hu.1))]
    simp only [mul_pow, div_pow, pow_add, pow_one]
    field_simp [hu.1.ne', hc.ne']
  change IntegrableOn g (Ioi 0) ∧ ∫ t in Ioi 0, g t = _
  rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj,
    integrableOn_congr_fun hweight measurableSet_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hweight]
  constructor
  · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  · rw [integral_div, integral_Ioo_pow_mul_one_sub_pow, Nat.add_comm k b, Nat.mul_comm k.factorial]

theorem integral_complex_norm_pow_div (c : ℝ) (hc : 0 < c) (k b : ℕ) :
    Integrable (fun w : ℂ => ‖w‖ ^ (2 * b) / (c + ‖w‖ ^ 2) ^ (b + 2 + k)) ∧
    ∫ w : ℂ, ‖w‖ ^ (2 * b) / (c + ‖w‖ ^ 2) ^ (b + 2 + k) =
      π * (((b.factorial * k.factorial : ℕ) : ℝ) / (b + k + 1).factorial / c ^ (k + 1)) := by
  obtain ⟨hI, hV⟩ := integral_Ioi_pow_div_add_pow c hc k b
  set f : ℝ → ℝ := fun r => r ^ (2 * b) / (c + r ^ 2) ^ (b + 2 + k) with hf
  set g : ℝ → ℝ := fun t => t ^ b / (c + t) ^ (b + 2 + k) with hg
  have hdim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hcongr : EqOn (fun x : ℝ => (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • g (x ^ (2:ℝ)))
      (fun y : ℝ => (2:ℝ) * (y ^ (Module.finrank ℝ ℂ - 1) • f y)) (Ioi 0) := by
    intro x _
    simp only [hf, hg, hdim, smul_eq_mul]
    rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two, pow_mul]
    norm_num
    ring
  have h2 : IntegrableOn (fun x : ℝ => (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • g (x ^ (2:ℝ))) (Ioi 0) :=
    (integrableOn_Ioi_comp_rpow_iff g two_ne_zero).mpr hI
  have h3 := (integrableOn_congr_fun hcongr measurableSet_Ioi).mp h2
  have h4 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • f y) (Ioi 0) := by
    have h5 : IntegrableOn (fun y : ℝ => (1/2 : ℝ) * (2 * (y ^ (Module.finrank ℝ ℂ - 1) • f y)))
        (Ioi 0) := h3.const_mul (1/2 : ℝ)
    refine h5.congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]; ring
  have hint : Integrable (fun w : ℂ => f ‖w‖) :=
    (integrable_fun_norm_addHaar (volume : Measure ℂ) (f := f)).mpr h4
  refine ⟨hint, ?_⟩
  show ∫ w : ℂ, f ‖w‖ = _
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  have hsub := integral_comp_rpow_Ioi g (two_ne_zero : (2:ℝ) ≠ 0)
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul] at hsub
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) f, hball, hdim]
  have : ∫ y in Ioi (0:ℝ), y ^ (2 - 1) • f y = (∫ t in Ioi (0:ℝ), g t) / 2 := by
    rw [← hsub, hdim]; ring
  rw [this, hV]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

theorem lintegral_pi_complex_monomial (k : ℕ) : ∀ (N : ℕ) (b : Fin N → ℕ) (c : ℝ), 0 < c →
    ∫⁻ z : Fin N → ℂ, ENNReal.ofReal ((∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) =
      ENNReal.ofReal (π ^ N * (∏ j, ((b j).factorial : ℝ)) * k.factorial /
        (∑ j, b j + N + k).factorial / c ^ (k + 1)) := by
  intro N
  induction N with
  | zero =>
    intro b c hc
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, add_zero, zero_add,
      pow_zero, one_mul]
    rw [lintegral_const, volume_pi, Measure.pi_univ]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    congr 1
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    rw [add_comm 1 k]
    field_simp
  | succ N ih =>
    intro b c hc
    set K := ∑ j : Fin N, b j.succ + N + k with hK
    let g : ℂ × (Fin N → ℂ) → ENNReal := fun p => ENNReal.ofReal ((‖p.1‖ ^ (2 * b 0) *
        ∏ j : Fin N, ‖p.2 j‖ ^ (2 * b j.succ)) /
        (c + (‖p.1‖ ^ 2 + ∑ j : Fin N, ‖p.2 j‖ ^ 2)) ^ (b 0 + 2 + K))
    have hgm : Measurable g := by fun_prop
    have e := volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0
    have hexp : ∑ j, b j + (N + 1) + 1 + k = b 0 + 2 + K := by
      rw [Fin.sum_univ_succ, hK]; omega
    have hcomp : ∀ z : Fin (N + 1) → ℂ, ENNReal.ofReal ((∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + (N + 1) + 1 + k)) =
        g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) 0 z) := by
      intro z
      rw [hexp]
      simp [g, MeasurableEquiv.piFinSuccAbove_apply, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.tail]
    rw [lintegral_congr hcomp, e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Measure.volume_eq_prod, lintegral_prod_symm _ hgm.aemeasurable]
    have hinner : ∀ y : Fin N → ℂ, ∫⁻ w : ℂ, g (w, y) = ENNReal.ofReal
        ((π * (((b 0).factorial * K.factorial : ℕ) : ℝ) / (b 0 + K + 1).factorial) *
          ((∏ j : Fin N, ‖y j‖ ^ (2 * b j.succ)) /
            (c + ∑ j, ‖y j‖ ^ 2) ^ (∑ j : Fin N, b j.succ + N + 1 + k))) := by
      intro y
      set A := ∏ j : Fin N, ‖y j‖ ^ (2 * b j.succ) with hA'
      set c' := c + ∑ j, ‖y j‖ ^ 2 with hc'd
      have hc' : 0 < c' := by positivity
      have hA : 0 ≤ A := by positivity
      obtain ⟨hI, hV⟩ := integral_complex_norm_pow_div c' hc' K (b 0)
      have hsplit : ∀ w : ℂ, g (w, y) = ENNReal.ofReal A *
          ENNReal.ofReal (‖w‖ ^ (2 * b 0) / (c' + ‖w‖ ^ 2) ^ (b 0 + 2 + K)) := by
        intro w
        simp only [g]
        rw [← ENNReal.ofReal_mul hA]
        congr 1
        rw [hc'd, hA', show c + (‖w‖ ^ 2 + ∑ j, ‖y j‖ ^ 2) = c + ∑ j, ‖y j‖ ^ 2 + ‖w‖ ^ 2 by ring]
        ring
      rw [lintegral_congr hsplit, lintegral_const_mul _ (by fun_prop),
        ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun w => by positivity),
        hV, ← ENNReal.ofReal_mul hA]
      congr 1
      rw [show ∑ j : Fin N, b j.succ + N + 1 + k = K + 1 by omega]
      have : (c' ^ (K + 1)) ≠ 0 := by positivity
      field_simp
    rw [lintegral_congr hinner]
    have hC : 0 ≤ π * (((b 0).factorial * K.factorial : ℕ) : ℝ) / (b 0 + K + 1).factorial := by
      positivity
    rw [lintegral_congr (fun y => ENNReal.ofReal_mul hC), lintegral_const_mul _ (by fun_prop),
      ih (fun j => b j.succ) c hc, ← ENNReal.ofReal_mul hC]
    congr 1
    rw [Fin.prod_univ_succ, show ∑ j, b j + (N + 1) + k = b 0 + K + 1 by
      rw [Fin.sum_univ_succ, hK]; omega]
    have h1 : (K.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((b 0 + K + 1).factorial : ℝ) ≠ 0 := by positivity
    have h3 : c ^ (k + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem integral_pi_complex_monomial (k N : ℕ) (b : Fin N → ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun z : Fin N → ℂ => (∏ j, ‖z j‖ ^ (2 * b j)) /
        (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) ∧
    ∫ z : Fin N → ℂ, (∏ j, ‖z j‖ ^ (2 * b j)) / (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k) =
      π ^ N * (∏ j, ((b j).factorial : ℝ)) * k.factorial / (∑ j, b j + N + k).factorial /
        c ^ (k + 1) := by
  have hnn : ∀ z : Fin N → ℂ, 0 ≤ (∏ j, ‖z j‖ ^ (2 * b j)) /
      (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k) := fun z => by positivity
  have hm : AEStronglyMeasurable (fun z : Fin N → ℂ => (∏ j, ‖z j‖ ^ (2 * b j)) /
      (c + ∑ j, ‖z j‖ ^ 2) ^ (∑ j, b j + N + 1 + k)) := by
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn), lintegral_pi_complex_monomial k N b c hc]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hm,
      lintegral_pi_complex_monomial k N b c hc, ENNReal.toReal_ofReal (by positivity)]

end GroundTheory.Heights₂.Heights
