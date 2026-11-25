module

public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.RectResidue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LFunctionBounds.ExpSumLowerBound

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRectF

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma neg_log_deriv_differentiableAt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {w : ℂ}
    (hL : DirichletCharacter.LFunction χ w ≠ 0) : DifferentiableAt ℂ (negLD χ) w := by
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hd' : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) w :=
    ((hLd.analyticAt w).deriv).differentiableAt
  show DifferentiableAt ℂ (fun s => -(deriv (DirichletCharacter.LFunction χ) s /
    DirichletCharacter.LFunction χ s)) w
  exact (hd'.div (hLd w) hL).neg

lemma perron_integrand_differentiableAt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) (hL : DirichletCharacter.LFunction χ w ≠ 0) :
    DifferentiableAt ℂ (Fchi χ y) w := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  show DifferentiableAt ℂ (fun w => negLD χ w * (y : ℂ) ^ w / (w * (w - 1))) w
  refine ((neg_log_deriv_differentiableAt hχ hL).mul ?_).div (by fun_prop) (mul_ne_zero h0 (sub_ne_zero.2 h1))
  exact DifferentiableAt.const_cpow (f := fun w => w) differentiableAt_id (Or.inl hy')

lemma perron_integrand_residue_at_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) :
    ∃ A : ℂ → ℂ, DifferentiableAt ℂ A 1 ∧
      ∀ᶠ z in 𝓝[≠] (1 : ℂ), Fchi χ y z - negLD χ 1 * (y : ℂ) / (z - 1) = A z := by
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hL1 : DirichletCharacter.LFunction χ 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  set h : ℂ → ℂ := fun z => negLD χ z * (y : ℂ) ^ z / z with hh
  have hs : IsOpen {z : ℂ | DirichletCharacter.LFunction χ z ≠ 0 ∧ z ≠ 0} :=
    (isOpen_ne.preimage hLd.continuous).inter isOpen_ne
  have h1s : (1 : ℂ) ∈ {z : ℂ | DirichletCharacter.LFunction χ z ≠ 0 ∧ z ≠ 0} := ⟨hL1, one_ne_zero⟩
  have hdiff : DifferentiableOn ℂ h {z : ℂ | DirichletCharacter.LFunction χ z ≠ 0 ∧ z ≠ 0} := by
    intro z hz
    exact (((neg_log_deriv_differentiableAt hχ hz.1).mul
      (DifferentiableAt.const_cpow (f := fun w => w) differentiableAt_id (Or.inl hy'))).div
        differentiableAt_id hz.2).differentiableWithinAt
  refine ⟨dslope h 1,
    ((Complex.differentiableOn_dslope (hs.mem_nhds h1s)).2 hdiff).differentiableAt (hs.mem_nhds h1s), ?_⟩
  have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ≠ 1 ∧ z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds (one_ne_zero : (1 : ℂ) ≠ 0))] with z hz1 hz0
    exact ⟨hz1, hz0⟩
  filter_upwards [hev] with z hz
  obtain ⟨hz1, hz0⟩ := hz
  rw [dslope_of_ne _ hz1, slope_def_field]
  simp only [hh, Fchi, cpow_one, div_one]
  field_simp [sub_ne_zero.2 hz1]

lemma perron_integrand_residue_real_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) {β : ℂ} (h0 : 0 < β.re) (h1 : β ≠ 1)
    (hLβ : DirichletCharacter.LFunction χ β = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    ∃ A : ℂ → ℂ, DifferentiableAt ℂ A β ∧
      ∀ᶠ z in 𝓝[≠] β, DirichletCharacter.LFunction χ z ≠ 0 ∧
        Fchi χ y z - (-((y : ℂ) ^ β / (β * (β - 1)))) / (z - β) = A z := by
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hβ0 : β ≠ 0 := fun h => by rw [h] at h0; simp at h0
  set L := DirichletCharacter.LFunction χ with hLdef
  set g := dslope L β with hg
  have hgd : Differentiable ℂ g := fun z =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).2 hLd.differentiableOn).differentiableAt
      Filter.univ_mem
  have hgβ : g β ≠ 0 := by rw [hg, dslope_same]; exact hd
  have hLz : ∀ z, L z = (z - β) * g z := by
    intro z
    have := sub_smul_dslope L β z
    rw [hLβ, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hderiv : ∀ z, deriv L z = g z + (z - β) * deriv g z := by
    intro z
    have hfun : L = fun z => (z - β) * g z := funext hLz
    have h1 : HasDerivAt (fun z => (z - β) * g z) (1 * g z + (z - β) * deriv g z) z :=
      ((hasDerivAt_id' z).sub_const β).mul (hgd z).hasDerivAt
    rw [hfun, h1.deriv]
    ring
  have hev : ∀ᶠ z in 𝓝[≠] β, z ≠ β ∧ g z ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 := by
    have h2 : ∀ᶠ z in 𝓝 β, g z ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 :=
      ((hgd β).continuousAt.eventually_ne hgβ).and
        ((show ∀ᶠ z in 𝓝 β, z ≠ 0 from isOpen_ne.mem_nhds hβ0).and
          (show ∀ᶠ z in 𝓝 β, z ≠ 1 from isOpen_ne.mem_nhds h1))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h2] with z hz hz'
    exact ⟨hz, hz'⟩
  set k : ℂ → ℂ := fun z => (y : ℂ) ^ z / (z * (z - 1)) with hk
  have hs : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} := isOpen_ne.inter isOpen_ne
  have hβs : β ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := ⟨hβ0, h1⟩
  have hkd : DifferentiableOn ℂ k {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
    intro z hz
    have hz' : DifferentiableAt ℂ (fun w : ℂ => (y : ℂ) ^ w / (w * (w - 1))) z :=
      (DifferentiableAt.const_cpow (f := fun w => w) differentiableAt_id (Or.inl hy')).div
        (by fun_prop) (mul_ne_zero hz.1 (sub_ne_zero.2 hz.2))
    exact hz'.differentiableWithinAt
  have hdk : DifferentiableAt ℂ (dslope k β) β :=
    ((Complex.differentiableOn_dslope (hs.mem_nhds hβs)).2 hkd).differentiableAt (hs.mem_nhds hβs)
  have hdg' : DifferentiableAt ℂ (deriv g) β := ((hgd.analyticAt β).deriv).differentiableAt
  refine ⟨fun z => -(dslope k β z) - deriv g z / g z * k z,
    hdk.neg.sub ((hdg'.div (hgd β) hgβ).mul ((hkd β hβs).differentiableAt (hs.mem_nhds hβs))), ?_⟩
  filter_upwards [hev] with z hz
  obtain ⟨hzβ, hgz, hz0, hz1⟩ := hz
  refine ⟨by rw [hLz]; exact mul_ne_zero (sub_ne_zero.2 hzβ) hgz, ?_⟩
  rw [dslope_of_ne _ hzβ, slope_def_field]
  have hLz' : ∀ z, DirichletCharacter.LFunction χ z = (z - β) * g z := hLz
  have hderiv' : ∀ z, deriv (DirichletCharacter.LFunction χ) z = g z + (z - β) * deriv g z := hderiv
  simp only [Fchi, negLD, hk, hderiv', hLz']
  field_simp [sub_ne_zero.2 hzβ, hgz, hz0, sub_ne_zero.2 hz1, hβ0, sub_ne_zero.2 h1]
  ring

open Formalism.HermitianLattices.Ext.PrimesInProgressions in
theorem rectangle_contour_shift_character : RectShiftChi := by
  intro q _ χ hχ y hy σ₁ σ₀ T B hσ₁ hσ₁1 hσ₀ hT hB hZ hBz
  let Z := B.image (fun β : ℝ => (β : ℂ))
  have hmem (ρ : ℂ) : ρ ∈ Z ↔ exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T := by
    constructor
    · rintro h
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 h
      simpa only [exLF_of_ne hχ, ofReal_re, ofReal_im, abs_zero] using
        (show DirichletCharacter.LFunction χ (β : ℂ) = 0 ∧ σ₁ < β ∧ 0 < T from
          ⟨hBz β hβ, (hB β hβ).1, hT⟩)
    · rintro ⟨hρ, h1, h2⟩
      obtain ⟨β, hβ, rfl⟩ := hZ ρ h1.le ((exLF_re_lt_one χ hρ).trans hσ₀).le h2.le
        (by simpa only [exLF_of_ne hχ] using hρ)
      exact Finset.mem_image_of_mem _ hβ
  have hedge (w : ℂ) (hw1 : σ₁ ≤ w.re) (hw2 : w.re ≤ σ₀) (hwT : |w.im| ≤ T)
      (hw : exLF χ w = 0) : σ₁ < w.re ∧ |w.im| < T := by
    obtain ⟨β, hβ, rfl⟩ := hZ w hw1 hw2 hwT (by simpa only [exLF_of_ne hχ] using hw)
    simpa using And.intro (hB β hβ).1 hT
  have hsum : ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ =
      ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) := by
    rw [Finset.sum_image (fun _ _ _ _ h => ofReal_injective h)]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hm := exOrd_eq_one χ (ρ := (β : ℂ))
      (by simpa only [exLF_of_ne hχ] using hBz β hβ)
      (by simpa only [exLF_of_ne hχ] using (hB β hβ).2.2)
    unfold exKer
    rw [hm, Nat.cast_one, one_mul]
  have he := ex_rect_Fchi χ y hy σ₁ σ₀ T hσ₁ hσ₁1 hσ₀ hT Z hmem hedge
  rw [hsum, ite_eq_right hχ, add_zero] at he
  unfold explicitFormulaConstant at he
  rw [exLF_of_ne hχ] at he
  simpa only [Fchi, negLD] using he

end Formalism.ZeroFreeDirichlet
