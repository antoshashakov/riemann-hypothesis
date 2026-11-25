module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxDefs
public import GroundTheory.AutomorphicForms.GL2.GJFELeviConv
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
public import GroundTheory.AutomorphicForms.GL2.GJFEBlock
public import GroundTheory.AutomorphicForms.GL2.GJFELeviMulti
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.WhittakerGroups
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
import Supplements.AutomorphicForms.GL2.LeviBlockFunctionalEquation

@[expose] public section

noncomputable section

open MeasureTheory Measure GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal ENNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

set_option linter.unusedSectionVars false

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [∀ n : ℕ, MeasurableSpace (GL (Fin n) F)] [∀ n : ℕ, BorelSpace (GL (Fin n) F)]
  {W : Type} [AddCommGroup W] [Module ℂ W]


variable (F W) in
def GxMulti (ψ : AddChar F Circle) (r : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = r →
  ∀ (d : ι → ℕ) [∀ i, NeZero (d i)] (μ : ∀ i, Measure (GL (Fin (d i)) F))
    [∀ i, (μ i).IsHaarMeasure]
    (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SecondCountableTopology H]
    (ρ : Representation ℂ ((∀ i, GL (Fin (d i)) F) × H) W), IsAdmissible ρ → ρ.IsIrreducible →
    ∀ α : ι → ℂ, (∀ i, α i ≠ 0) →
      (∀ i v, ρ (Pi.mulSingle i (centralUnif F (d i)), 1) v = α i • v) →
      (∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        ∃ C : Set (∀ i, GL (Fin (d i)) F), IsCompact C ∧
          ∀ x, ℓ (ρ (x, 1) v) ≠ 0 → ∃ j : ι → ℤ, (fun i => centralUnif F (d i) ^ j i) * x ∈ C) →
    ∃ γ : RatFunc ℂ, GxShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ
        (∏ i, if d i = 1 ∧ ∀ g ∈ integralGL F (d i), ρ (Pi.mulSingle i g, 1) = 1 then
          1 - Polynomial.C (α i) * Polynomial.X else 1) ∧
      ∀ Ψ : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ,
      (∀ i, IsSchwartzBruhat (Ψ i)) → ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        RatFE F γ (fun s => ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ)
          (fun s => ∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x
            ∂Measure.pi μ)

theorem gxMulti_zero (ψ : AddChar F Circle) : GxMulti F W ψ 0 := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ _ ρ _ _ α _ _ _
  have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
  refine ⟨1, by simpa using gxShape_one _, fun Ψ _ w ℓ _ => ?_⟩
  have hval : ∀ f : (∀ i, GL (Fin (d i)) F) → ℂ,
      ∫ x, f x ∂Measure.pi μ = f 1 := by
    intro f
    have hu : (Measure.pi μ).real Set.univ = 1 := by
      rw [Measure.real, Measure.pi_of_empty μ (1 : ∀ i, GL (Fin (d i)) F), measure_univ,
        ENNReal.toReal_one]
    rw [integral_unique, hu, one_smul]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨RatFunc.C (ℓ w), 0, fun s _ => ?_, fun s _ => ?_⟩
  · show ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ = _
    rw [hval, RatFunc.eval_C]
    simp only [multiA, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    rw [show ((1 : ∀ i, GL (Fin (d i)) F), (1 : H)) = 1 from rfl, map_one]
    rfl
  · show ∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x ∂Measure.pi μ = _
    rw [hval, one_mul, RatFunc.eval_C]
    simp only [multiB, Finset.univ_eq_empty, Finset.prod_empty, one_mul, inv_one]
    rw [show ((1 : ∀ i, GL (Fin (d i)) F), (1 : H)) = 1 from rfl, map_one]
    rfl

theorem gxMulti_succ (hB : GxBlock) {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {r : ℕ}
    (ih : GxMulti F W ψ r) : GxMulti F W ψ (r + 1) := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ _ ρ hadm hirr α hα0 hα hsupp
  obtain ⟨a⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)

  set ρ₁ : Representation ℂ (GL (Fin (d a)) F × ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H)) W :=
    ρ.comp (peelFst d H a).symm.toMonoidHom with hρ₁def
  set ρ₂ : Representation ℂ ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × (GL (Fin (d a)) F × H)) W :=
    ρ.comp (peelSnd d H a).symm.toMonoidHom with hρ₂def
  have hρ₁ : ∀ g y h, ρ₁ (g, (y, h)) = ρ (splitSymm d a g y, h) := fun g y h => by
    rw [hρ₁def, MonoidHom.comp_apply]
    exact congrArg ρ (peelFst_symm_apply d H a (g, (y, h)))
  have hρ₂ : ∀ y g h, ρ₂ (y, (g, h)) = ρ (splitSymm d a g y, h) := fun y g h => by
    rw [hρ₂def, MonoidHom.comp_apply]
    exact congrArg ρ (peelSnd_symm_apply d H a (y, (g, h)))
  have hadm₁ : IsAdmissible ρ₁ := (isAdmissible_comp_iff (peelFst d H a).symm ρ).2 hadm
  have hadm₂ : IsAdmissible ρ₂ := (isAdmissible_comp_iff (peelSnd d H a).symm ρ).2 hadm
  have hirr₁ : ρ₁.IsIrreducible := (isIrreducible_comp_iff (peelFst d H a).symm ρ).2 hirr
  have hirr₂ : ρ₂.IsIrreducible := (isIrreducible_comp_iff (peelSnd d H a).symm ρ).2 hirr
  have hsm₁ : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors (Representation.dual ρ₁) ↔
      ℓ ∈ smoothVectors (Representation.dual ρ) := fun ℓ =>
    mem_smoothVectors_dual_comp_iff (peelFst d H a).symm ρ
  have hsm₂ : ∀ ℓ : Module.Dual ℂ W, ℓ ∈ smoothVectors (Representation.dual ρ₂) ↔
      ℓ ∈ smoothVectors (Representation.dual ρ) := fun ℓ =>
    mem_smoothVectors_dual_comp_iff (peelSnd d H a).symm ρ

  have hα₁ : ∀ v, ρ₁ (centralUnif F (d a), 1) v = α a • v := by
    intro v
    change ρ₁ (centralUnif F (d a), ((1 : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F), (1 : H))) v = _
    rw [hρ₁, splitSymm_mulSingle_self]
    exact hα a v
  have hsupp₁ : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ₁),
      ∃ C : Set (GL (Fin (d a)) F), IsCompact C ∧
        ∀ g, ℓ (ρ₁ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F (d a) ^ j * g ∈ C := by
    intro v ℓ hℓ
    obtain ⟨C, hC, hCs⟩ := hsupp v ℓ ((hsm₁ ℓ).1 hℓ)
    refine ⟨(fun x : ∀ i, GL (Fin (d i)) F => x a) '' C, hC.image (continuous_apply a),
      fun g hg => ?_⟩
    change ℓ (ρ₁ (g, ((1 : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F), (1 : H))) v) ≠ 0 at hg
    rw [hρ₁, splitSymm_mulSingle_self] at hg
    obtain ⟨j, hj⟩ := hCs _ hg
    exact ⟨j a, _, hj, by simp [Pi.mul_apply]⟩
  obtain ⟨γa, sa, hblock⟩ := exists_blockFE (μ a) hadm₁ hψ hψ1 hα₁ hsupp₁
  have hsh₁ := hB F (d a) (μ a) _ W ρ₁ hadm₁ hirr₁ (α a) (hα0 a) hα₁ hsupp₁ ψ hψ hψ1 γa
    (fun Φ hΦ v ℓ hℓ => (hblock Φ hΦ v ℓ hℓ).2.2)

  have hcard' : Fintype.card {i // i ≠ a} = r := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, hcard]
    rfl
  have hα₂ : ∀ (j : {i // i ≠ a}) v, ρ₂ (Pi.mulSingle j (centralUnif F (d j)), 1) v = α j • v := by
    intro j v
    change ρ₂ (Pi.mulSingle j (centralUnif F (d j)), ((1 : GL (Fin (d a)) F), (1 : H))) v = _
    rw [hρ₂, splitSymm_one_mulSingle]
    exact hα j v
  have hsupp₂ : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ₂),
      ∃ C : Set (∀ i : {i // i ≠ a}, GL (Fin (d i)) F), IsCompact C ∧
        ∀ y, ℓ (ρ₂ (y, 1) v) ≠ 0 →
          ∃ j : {i // i ≠ a} → ℤ,
            (fun i : {i // i ≠ a} => centralUnif F (d i) ^ j i) * y ∈ C := by
    intro v ℓ hℓ
    obtain ⟨C, hC, hCs⟩ := hsupp v ℓ ((hsm₂ ℓ).1 hℓ)
    refine ⟨(fun x : ∀ i, GL (Fin (d i)) F => fun k : {i // i ≠ a} => x k) '' C,
      hC.image (continuous_pi fun k => continuous_apply (k : ι)), fun y hy => ?_⟩
    change ℓ (ρ₂ (y, ((1 : GL (Fin (d a)) F), (1 : H))) v) ≠ 0 at hy
    rw [hρ₂] at hy
    obtain ⟨j, hj⟩ := hCs _ hy
    refine ⟨fun k => j k, _, hj, ?_⟩
    funext k
    exact centralPow_mul_splitSymm_apply j y k
  obtain ⟨γ', hsh₂, hIH⟩ := ih {i // i ≠ a} hcard' (fun j => d j) (fun j => μ j) (GL (Fin (d a)) F × H) ρ₂
    hadm₂ hirr₂ (fun j => α j) (fun j => hα0 j) hα₂ hsupp₂

  obtain ⟨s₀, hconv⟩ := exists_integrable_multi ρ hadm.1 hα0 hα hsupp μ
  obtain ⟨s₂, hconv₂⟩ := exists_integrable_multi ρ₂ hadm₂.1 (fun j => hα0 j) hα₂ hsupp₂
    (fun j => μ j)
  refine ⟨γa * γ', ?_, fun Ψ hΨ w ℓ hℓ => ?_⟩
  · have e₁ : ∀ g : GL (Fin (d a)) F, ρ₁ (g, 1) = ρ (Pi.mulSingle a g, 1) := fun g => by
      change ρ₁ (g, ((1 : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F), (1 : H))) = _
      rw [hρ₁, splitSymm_mulSingle_self]
    have e₂ : ∀ (j : {i // i ≠ a}) (g : GL (Fin (d j)) F),
        ρ₂ (Pi.mulSingle j g, 1) = ρ (Pi.mulSingle (j : ι) g, 1) := fun j g => by
      change ρ₂ (Pi.mulSingle j g, ((1 : GL (Fin (d a)) F), (1 : H))) = _
      rw [hρ₂, splitSymm_one_mulSingle]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ a]
    simp only [e₁, e₂] at hsh₁ hsh₂
    exact gxShape_mul hsh₁ hsh₂
  exact block_mul_tail_FE hψ hψ1 hρ₁ hρ₂ hadm₁ hΨ hℓ
    ((hsm₁ ℓ).2 hℓ) ((hsm₂ ℓ).2 hℓ) hblock hIH hconv hconv₂
    (blockA_eq_sum (μ₀ := μ a) hadm₁.1) (blockB_eq_sum (μ₀ := μ a) hadm₁.1)

theorem gxMulti_all (hB : GxBlock) {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∀ r, GxMulti F W ψ r
  | 0 => gxMulti_zero ψ
  | r + 1 => gxMulti_succ hB hψ hψ1 (gxMulti_all hB hψ hψ1 r)

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
