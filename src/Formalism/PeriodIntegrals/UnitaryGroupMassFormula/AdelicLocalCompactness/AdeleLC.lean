module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntegralApproximation

@[expose] public section

noncomputable section

namespace PI.AdicCompletionValuation

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped RestrictedProduct

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem algebraMap_mem_integer (r : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ∈ Valued.integer (v.adicCompletion F) := by
  have h := v.coe_mem_adicCompletionIntegers (K := F) r
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  exact h

private theorem exists_ringOfIntegers_valuation_sub_lt_one_of_le (k : F) (hk : v.valuation F k ≤ 1) :
    ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) < 1 := by
  first
  | exact @_root_.Formalism.L2.SG.IntegralApproximation.exists_int_approx
  | exact _root_.Formalism.L2.SG.IntegralApproximation.exists_int_approx
  | (apply _root_.Formalism.L2.SG.IntegralApproximation.exists_int_approx <;> assumption)
  | (intros; apply _root_.Formalism.L2.SG.IntegralApproximation.exists_int_approx <;> assumption)
  | (intros; apply @_root_.Formalism.L2.SG.IntegralApproximation.exists_int_approx <;> first | assumption | infer_instance)
  | (intros; exact _root_.Formalism.L2.SG.IntegralApproximation.exists_int_approx ..)

private theorem valued_algebraMap_adicCompletion_eq_valuation' (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k := by
  exact valuedAdicCompletion_eq_valuation' v k

private theorem valued_algebraMap_ringOfIntegers_eq_intValuation (a : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) = v.intValuation a := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), valued_algebraMap_adicCompletion_eq_valuation']
  exact valuation_of_algebraMap v a

private theorem denseRange_algebraMap_adicCompletion' : DenseRange (algebraMap F (v.adicCompletion F)) := by
  first
  | exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.denseRange_coe F v
  | exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v
  | exact IsDedekindDomain.HeightOneSpectrum.denseRange_coe F v
  | exact (v.valuation F).denseRange_coe
  | exact Valuation.Completion.denseRange_coe
  | exact UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation F))
  | (intro x; exact UniformSpace.Completion.denseRange_coe x)
  | exact (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation F))).comp
      (WithVal.equiv (v.valuation F)).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)
  | exact @UniformSpace.Completion.denseRange_coe F v.adicValued.toUniformSpace
  | (letI := v.adicValued; exact UniformSpace.Completion.denseRange_coe)
  | (refine Dense.mono ?_ (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation F)))
     rintro _ ⟨y, rfl⟩
     first
     | exact ⟨WithVal.equiv _ y, rfl⟩
     | exact ⟨WithVal.ofVal y, rfl⟩
     | exact ⟨y, rfl⟩
     | exact ⟨WithVal.equiv _ y, by simp⟩
     | exact ⟨WithVal.ofVal y, by simp⟩)
  | (delta IsDedekindDomain.HeightOneSpectrum.adicCompletion
     exact UniformSpace.Completion.denseRange_coe)
  | (unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion Valuation.Completion
     refine Dense.mono ?_ UniformSpace.Completion.denseRange_coe
     rintro _ ⟨y, rfl⟩
     first
     | exact ⟨WithVal.equiv _ y, rfl⟩
     | exact ⟨WithVal.ofVal y, rfl⟩
     | exact ⟨y, rfl⟩)

private theorem exists_ringOfIntegers_valued_sub_lt_one_of_le_one (x : v.adicCompletion F) (hx : Valued.v x ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  obtain ⟨π, hπp, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hvP : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) < 1 := by
    rw [valued_algebraMap_ringOfIntegers_eq_intValuation]
    exact (intValuation_lt_one_iff_mem v π).mpr hπp
  have hP0 : algebraMap (𝓞 F) (v.adicCompletion F) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hπ0)
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  have hW : IsOpen ((fun y => (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (y - x)) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
    apply hO.preimage
    exact continuous_const.mul (continuous_id.sub continuous_const)
  have hxW : x ∈ ((fun y => (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (y - x)) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
    show (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ * (x - x) ∈ v.adicCompletionIntegers F
    rw [sub_self, mul_zero]
    exact zero_mem _
  obtain ⟨k, hk⟩ := (denseRange_algebraMap_adicCompletion' F v).exists_mem_open hW ⟨x, hxW⟩
  have h1 : (algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ *
      (algebraMap F (v.adicCompletion F) k - x) ∈ v.adicCompletionIntegers F := hk
  have h2 := (mem_adicCompletionIntegers (𝓞 F) F v).mp h1
  have hk' : Valued.v (algebraMap F (v.adicCompletion F) k - x) < 1 := by
    have e : algebraMap F (v.adicCompletion F) k - x =
        algebraMap (𝓞 F) (v.adicCompletion F) π * ((algebraMap (𝓞 F) (v.adicCompletion F) π)⁻¹ *
          (algebraMap F (v.adicCompletion F) k - x)) := by
      rw [mul_inv_cancel_left₀ hP0]
    rw [e, map_mul]
    calc _ ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) π) * 1 := by
          first
          | exact mul_le_mul_left' h2 _
          | gcongr
      _ < 1 := by rw [mul_one]; exact hvP
  have hkv : v.valuation F k ≤ 1 := by
    rw [← valued_algebraMap_adicCompletion_eq_valuation' F v k]
    have h3 := Valuation.map_add_le (v := Valued.v) hk'.le hx
    rwa [sub_add_cancel] at h3
  obtain ⟨r, hr⟩ := exists_ringOfIntegers_valuation_sub_lt_one_of_le F v k hkv
  refine ⟨r, ?_⟩
  have e : x - algebraMap (𝓞 F) (v.adicCompletion F) r =
      (x - algebraMap F (v.adicCompletion F) k) +
        algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F r) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    ring
  rw [e]
  refine Valuation.map_add_lt (v := Valued.v) ?_ ?_
  · rw [Valuation.map_sub_swap]
    exact hk'
  · rw [valued_algebraMap_adicCompletion_eq_valuation']
    exact hr

private theorem mem_maximalIdeal_of_valued_lt_one (d : Valued.integer (v.adicCompletion F))
    (hd : Valued.v (d : v.adicCompletion F) < 1) :
    d ∈ IsLocalRing.maximalIdeal (Valued.integer (v.adicCompletion F)) := by
  show ¬ IsUnit d
  intro hu
  have h1 : Valued.v (d : v.adicCompletion F) = 1 := by
    exact (Valuation.integer.integers
      (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one.mp hu
  exact (ne_of_lt hd) h1

theorem finite_residueField :
    Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))) := by
  apply PI.WAU.finite_residue <;> assumption

instance compactSpace_integer : CompactSpace (Valued.integer (v.adicCompletion F)) := by
  haveI : IsDiscreteValuationRing (Valued.integer (v.adicCompletion F)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  haveI : CompleteSpace (Valued.integer (v.adicCompletion F)) :=
    (Valued.isClosed_integer (v.adicCompletion F)).completeSpace_coe
  haveI := finite_residueField F v
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, this⟩

theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have : CompactSpace (Valued.integer (v.adicCompletion F)) := compactSpace_integer F v
  exact isCompact_iff_compactSpace.mpr this

instance locallyCompactSpace_finiteAdeleRing : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v => isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers F v)
  exact inferInstanceAs (LocallyCompactSpace (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

instance locallyCompactSpace_adeleRing : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

instance t2Space_infiniteAdeleRing : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

instance t2Space_adeleRing : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end PI.AdicCompletionValuation
