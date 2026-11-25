module

public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.ProjectiveLattices.PtFree
public import Formalism.LocalToGlobal.ProjectiveLattices.LocFld

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open Formalism.L2.Pj Formalism.L2.PjFree
open IsDedekindDomain NumberField HeightOneSpectrum Filter
open scoped WithZero Topology

namespace AdicCompl

lemma lt_one_iff_le (g : ℤᵐ⁰) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

section Compl

variable {R : Type} [CommRing R] [IsDedekindDomain R] {L : Type} [Field L] [Algebra R L]
  [IsFractionRing R L] (w : HeightOneSpectrum R)

local notation "Lw" => w.adicCompletion L
local notation "Ow" => w.adicCompletionIntegers L

lemma v_algebraMap (l : L) : Valued.v (algebraMap L Lw l) = w.valuation L l :=
  valuedAdicCompletion_eq_valuation' w l

lemma exists_unif : ∃ π : Ow, Valued.v (π : Lw) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have h : Valued.v (algebraMap L Lw π) = WithZero.exp (-1 : ℤ) := by
    rw [v_algebraMap, hπ]
  refine ⟨⟨algebraMap L Lw π, ?_⟩, h⟩
  rw [mem_adicCompletionIntegers, h]
  exact ((lt_one_iff_le _).2 le_rfl).le

lemma mem_max_iff (x : Ow) :
    x ∈ IsLocalRing.maximalIdeal Ow ↔ Valued.v (x : Lw) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have : Valued.v (x : Lw) ≤ 1 := (mem_adicCompletionIntegers R L w).1 x.2
  exact ⟨fun h => lt_of_le_of_ne this h, fun h => h.ne⟩

lemma max_eq_span {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal Ow = Ideal.span {π} := by
  ext x
  rw [mem_max_iff, Ideal.mem_span_singleton, lt_one_iff_le, ← hπ]
  exact (adicCompletionIntegers.integers L w).le_iff_dvd

lemma mem_max_pow_iff {π : Ow} (hπ : Valued.v (π : Lw) = WithZero.exp (-1 : ℤ)) (x : Ow) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal Ow ^ n ↔ Valued.v (x : Lw) ≤ Valued.v (π : Lw) ^ n := by
  rw [max_eq_span w hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have := (adicCompletionIntegers.integers L w).le_iff_dvd (x := x) (y := π ^ n)
  rw [map_pow, map_pow] at this
  exact this.symm

theorem isPrecomplete : IsPrecomplete (IsLocalRing.maximalIdeal Ow) Ow := by
  first
  | exact _root_.Formalism.L2.Pj.LocFldPf.isPrecomplete
  | (apply _root_.Formalism.L2.Pj.LocFldPf.isPrecomplete <;> assumption)

theorem isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal Ow) Ow :=
  { toIsHausdorff := inferInstance, toIsPrecomplete := isPrecomplete w }

lemma finite_res [Finite (R ⧸ w.asIdeal)] : Finite (IsLocalRing.ResidueField Ow) := by
  let φ : R →+* IsLocalRing.ResidueField Ow := (IsLocalRing.residue Ow).comp (algebraMap R Ow)
  have h0 : ∀ a ∈ w.asIdeal, φ a = 0 := by
    intro a ha
    show IsLocalRing.residue Ow (algebraMap R Ow a) = 0
    rw [IsLocalRing.residue_eq_zero_iff, mem_max_iff, algebraMap_adicCompletionIntegers_apply,
      valuedAdicCompletion_eq_valuation', valuation_lt_one_iff_mem]
    exact ha
  refine Finite.of_surjective (Ideal.Quotient.lift w.asIdeal φ h0) ?_
  apply Ideal.Quotient.lift_surjective_of_surjective
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hU : {y : Lw | (Valued.v : Valuation Lw ℤᵐ⁰).restrict (y - (x : Lw)) < 1} ∈ 𝓝 (x : Lw) := by
    rw [Valued.mem_nhds]
    exact ⟨1, subset_rfl⟩
  obtain ⟨l, hl⟩ := (denseRange_algebraMap L w).mem_nhds hU
  have hl' : Valued.v (algebraMap L Lw l - (x : Lw)) < 1 := by
    have : (Valued.v : Valuation Lw ℤᵐ⁰).restrict (algebraMap L Lw l - (x : Lw)) < 1 := hl
    rwa [Valuation.restrict_lt_iff_lt_embedding, map_one] at this
  have hl1 : w.valuation L l ≤ 1 := by
    rw [← v_algebraMap]
    have e : algebraMap L Lw l = (algebraMap L Lw l - (x : Lw)) + (x : Lw) := by ring
    rw [e]
    exact Valuation.map_add_le _ hl'.le ((mem_adicCompletionIntegers R L w).1 x.2)
  obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer hl1 1
  refine ⟨a, ?_⟩
  show IsLocalRing.residue Ow (algebraMap R Ow a) = IsLocalRing.residue Ow x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  have e : ((algebraMap R Ow a - x : Ow) : Lw) =
      algebraMap L Lw (algebraMap R L a - l) + (algebraMap L Lw l - (x : Lw)) := by
    have h1 : ((algebraMap R Ow a : Ow) : Lw) = algebraMap L Lw (algebraMap R L a) := by
      rw [algebraMap_adicCompletionIntegers_apply]
      rfl
    rw [AddSubgroupClass.coe_sub, h1, map_sub]
    ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ hl'
  rw [v_algebraMap]
  simpa using ha

def kMap : L →+* FractionRing Ow :=
  ((FractionRing.algEquiv Ow Lw).symm : Lw →+* FractionRing Ow).comp (algebraMap L Lw)

lemma exists_e : ∃ e : ℕ, 0 < e ∧ ∀ x : L, valV Ow (kMap w x) = w.valuation L x ^ e := by
  let : Algebra L (FractionRing Ow) := (kMap w).toAlgebra
  have : IsScalarTower R L (FractionRing Ow) := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R Ow (FractionRing Ow)]
    show _ = (FractionRing.algEquiv Ow Lw).symm (algebraMap L Lw (algebraMap R L r))
    have : algebraMap L Lw (algebraMap R L r) = algebraMap Ow Lw (algebraMap R Ow r) := by
      show _ = ((algebraMap R Ow r : Ow) : Lw)
      rw [algebraMap_adicCompletionIntegers_apply]
      rfl
    rw [this, AlgEquiv.commutes]
  let m : HeightOneSpectrum Ow := IsDiscreteValuationRing.maximalIdeal Ow
  have : m.asIdeal.LiesOver w.asIdeal := ⟨by
    ext a
    rw [Ideal.mem_comap]
    show _ ↔ algebraMap R Ow a ∈ IsLocalRing.maximalIdeal Ow
    rw [mem_max_iff, algebraMap_adicCompletionIntegers_apply,
      valuedAdicCompletion_eq_valuation', valuation_lt_one_iff_mem]⟩
  exact ⟨w.asIdeal.ramificationIdx' m.asIdeal,
    Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver m.asIdeal w.ne_bot),
    fun x => by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal m.asIdeal w.ne_bot]
      exact (valuation_liesOver (FractionRing Ow) w m x).symm⟩

end Compl

end AdicCompl


open AdicCompl in
theorem locFld : Formalism.L2.PjFree.LocFld :=
  _root_.Formalism.L2.Pj.locFld

end GlobalTheory
