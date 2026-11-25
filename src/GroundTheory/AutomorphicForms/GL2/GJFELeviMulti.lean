module

public import GroundTheory.AutomorphicForms.GL2.GJFELeviPeel
public import GroundTheory.AutomorphicForms.GL2.GJFELeviConv
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
public import GroundTheory.AutomorphicForms.GL2.GJFEBlock
import GroundTheory.AutomorphicForms.GL2.GJInducedZeta
import GroundTheory.AutomorphicForms.LocallyProfinite
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Supplements.AutomorphicForms.GL2.LeviBlockFunctionalEquation

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal MeasureTheory Measure Parabolic
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

universe uF u w

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

section SplitFacts

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ} {a : ι}

theorem splitSymm_mulSingle_self (c : GL (Fin (d a)) F) :
    splitSymm d a c 1 = (Pi.mulSingle a c : ∀ i, GL (Fin (d i)) F) := by
  funext i
  by_cases hi : i = a
  · subst hi; simp
  · have := splitSymm_apply_ne (d := d) c 1 ⟨i, hi⟩
    simp only at this
    rw [this, Pi.mulSingle_eq_of_ne hi]
    rfl

theorem splitSymm_one_mulSingle (j : {i // i ≠ a}) (c : GL (Fin (d j)) F) :
    splitSymm d a 1 (Pi.mulSingle j c) = (Pi.mulSingle (j : ι) c : ∀ i, GL (Fin (d i)) F) := by
  funext i
  by_cases hi : i = a
  · subst hi
    rw [splitSymm_apply_self, Pi.mulSingle_eq_of_ne (Ne.symm j.2)]
  · have := splitSymm_apply_ne (d := d) 1 (Pi.mulSingle j c) ⟨i, hi⟩
    simp only at this
    rw [this]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Pi.mulSingle_eq_of_ne (show (⟨i, hi⟩ : {i // i ≠ a}) ≠ j from fun h => hij (by rw [← h])),
        Pi.mulSingle_eq_of_ne hij]

theorem prod_splitSymm {M : Type*} [CommMonoid M] (f : ∀ i, GL (Fin (d i)) F → M)
    (g : GL (Fin (d a)) F) (y : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F) :
    ∏ i, f i (splitSymm d a g y i) = f a g * ∏ j : {i // i ≠ a}, f j (y j) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ a, splitSymm_apply_self]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [splitSymm_apply_ne]

theorem centralPow_mul_splitSymm_apply (j : ι → ℤ) (y : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F)
    (k : {i // i ≠ a}) :
    ((fun i => centralUnif F (d i) ^ j i) * splitSymm d a 1 y) k =
      centralUnif F (d k) ^ j k * y k := by
  rw [Pi.mul_apply, splitSymm_apply_ne]

end SplitFacts

section BlockDecomp

variable [MeasurableSpace F] [BorelSpace F] {m : ℕ} [MeasurableSpace (GL (Fin m) F)]
  [BorelSpace (GL (Fin m) F)] {H₁ : Type*} [Group H₁] [TopologicalSpace H₁]
  [IsTopologicalGroup H₁] [LocallyCompactSpace H₁] [T2Space H₁] [TotallyDisconnectedSpace H₁]
  {W : Type*} [AddCommGroup W] [Module ℂ W] (μ₀ : Measure (GL (Fin m) F)) [μ₀.IsHaarMeasure]
  {ρ₁ : Representation ℂ (GL (Fin m) F × H₁) W}

def blockALin (Ψ : Matrix (Fin m) (Fin m) F → ℂ) (w : W) (s : ℂ)
    (hint : ∀ μ ∈ smoothVectors (Representation.dual ρ₁),
      Integrable (fun g : GL (Fin m) F => Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        μ (ρ₁ (g, 1) w)) μ₀) :
    smoothVectors (Representation.dual ρ₁) →ₗ[ℂ] ℂ where
  toFun μ := blockA μ₀ ρ₁ Ψ w μ s
  map_add' μ ν := by
    simp only [blockA, Submodule.coe_add, LinearMap.add_apply, mul_add]
    exact integral_add (hint μ μ.2) (hint ν ν.2)
  map_smul' c μ := by
    simp only [blockA, SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1
    funext g
    ring

def blockBLin (Φ : Matrix (Fin m) (Fin m) F → ℂ) (w : W) (s : ℂ)
    (hint : ∀ μ ∈ smoothVectors (Representation.dual ρ₁),
      Integrable (fun g : GL (Fin m) F => Φ (g : Matrix (Fin m) (Fin m) F) * detPow g (m - s) *
        μ (ρ₁ (g⁻¹, 1) w)) μ₀) :
    smoothVectors (Representation.dual ρ₁) →ₗ[ℂ] ℂ where
  toFun μ := blockB μ₀ ρ₁ Φ w μ s
  map_add' μ ν := by
    simp only [blockB, Submodule.coe_add, LinearMap.add_apply, mul_add]
    exact integral_add (hint μ μ.2) (hint ν ν.2)
  map_smul' c μ := by
    simp only [blockB, SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1
    funext g
    ring

variable {μ₀}

theorem rep_inv_mul_prod {Ka : Subgroup (GL (Fin m) F)} {K' : Subgroup H₁} {w : W}
    (hw : w ∈ fixedVectors ρ₁ (Ka.prod K')) {k : GL (Fin m) F × H₁} (hk : k ∈ Ka.prod K')
    (g : GL (Fin m) F) : ρ₁ k⁻¹ (ρ₁ (g, 1) w) = ρ₁ (k.1⁻¹ * g, 1) w := by
  have h2 : ((1 : GL (Fin m) F), k.2⁻¹) ∈ Ka.prod K' :=
    Subgroup.mem_prod.2 ⟨one_mem _, inv_mem (Subgroup.mem_prod.1 hk).2⟩
  have : k⁻¹ * (g, 1) = (k.1⁻¹ * g, 1) * (1, k.2⁻¹) := by
    ext1 <;> simp
  rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply, hw _ h2]

theorem blockA_eq_sum (hρ₁ : IsSmooth ρ₁) {Ka : Subgroup (GL (Fin m) F)} {K' : Subgroup H₁}
    (hKc : IsCompact ((Ka.prod K' : Subgroup (GL (Fin m) F × H₁)) : Set (GL (Fin m) F × H₁)))
    (hKo : IsOpen ((Ka.prod K' : Subgroup (GL (Fin m) F × H₁)) : Set (GL (Fin m) F × H₁)))
    [FiniteDimensional ℂ (fixedVectors ρ₁ (Ka.prod K'))] (hKa : Ka ≤ integralGL F m)
    {Ψ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΨ : ∀ k ∈ Ka, ∀ X, Ψ ((k : Matrix (Fin m) (Fin m) F) * X) = Ψ X)
    {w : W} (hw : w ∈ fixedVectors ρ₁ (Ka.prod K')) {s : ℂ}
    (hint : ∀ μ ∈ smoothVectors (Representation.dual ρ₁),
      Integrable (fun g : GL (Fin m) F => Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        μ (ρ₁ (g, 1) w)) μ₀)
    (μ : smoothVectors (Representation.dual ρ₁)) :
    blockA μ₀ ρ₁ Ψ w μ s = ∑ i, (μ : Module.Dual ℂ W)
        (Module.finBasis ℂ (fixedVectors ρ₁ (Ka.prod K')) i : W) *
      blockA μ₀ ρ₁ Ψ w (((extendFixed hρ₁ hKc hKo
        ((Module.finBasis ℂ (fixedVectors ρ₁ (Ka.prod K'))).coord i) :
          fixedVectors (contragredient ρ₁) (Ka.prod K')) : smoothVectors (Representation.dual ρ₁)) :
            Module.Dual ℂ W) s := by
  refine eq_sum_of_invariant hρ₁ hKc hKo (blockALin μ₀ Ψ w s hint) ?_ μ
  intro k hk ν
  show blockA μ₀ ρ₁ Ψ w (contragredient ρ₁ k ν : smoothVectors _) s = blockA μ₀ ρ₁ Ψ w ν s
  simp only [blockA, contragredient_apply_apply]
  have hk1 : k.1 ∈ Ka := (Subgroup.mem_prod.1 hk).1
  simp_rw [rep_inv_mul_prod hw hk]
  rw [← integral_mul_left_eq_self _ k.1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [inv_mul_cancel_left, Units.val_mul, hΨ k.1 hk1]
  rw [detPow_mul, detPow_of_mem_integralGL (hKa hk1), one_mul]

theorem blockB_eq_sum (hρ₁ : IsSmooth ρ₁) {Ka : Subgroup (GL (Fin m) F)} {K' : Subgroup H₁}
    (hKc : IsCompact ((Ka.prod K' : Subgroup (GL (Fin m) F × H₁)) : Set (GL (Fin m) F × H₁)))
    (hKo : IsOpen ((Ka.prod K' : Subgroup (GL (Fin m) F × H₁)) : Set (GL (Fin m) F × H₁)))
    [FiniteDimensional ℂ (fixedVectors ρ₁ (Ka.prod K'))] (hKa : Ka ≤ integralGL F m)
    {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : ∀ k ∈ Ka, ∀ X, Φ (X * (k : Matrix (Fin m) (Fin m) F)) = Φ X)
    {w : W} (hw : w ∈ fixedVectors ρ₁ (Ka.prod K')) {s : ℂ}
    (hint : ∀ μ ∈ smoothVectors (Representation.dual ρ₁),
      Integrable (fun g : GL (Fin m) F => Φ (g : Matrix (Fin m) (Fin m) F) * detPow g (m - s) *
        μ (ρ₁ (g⁻¹, 1) w)) μ₀)
    (μ : smoothVectors (Representation.dual ρ₁)) :
    blockB μ₀ ρ₁ Φ w μ s = ∑ i, (μ : Module.Dual ℂ W)
        (Module.finBasis ℂ (fixedVectors ρ₁ (Ka.prod K')) i : W) *
      blockB μ₀ ρ₁ Φ w (((extendFixed hρ₁ hKc hKo
        ((Module.finBasis ℂ (fixedVectors ρ₁ (Ka.prod K'))).coord i) :
          fixedVectors (contragredient ρ₁) (Ka.prod K')) : smoothVectors (Representation.dual ρ₁)) :
            Module.Dual ℂ W) s := by
  have : μ₀.IsMulRightInvariant := Measures.isMulRightInvariant_GL F m μ₀
  refine eq_sum_of_invariant hρ₁ hKc hKo (blockBLin μ₀ Φ w s hint) ?_ μ
  intro k hk ν
  show blockB μ₀ ρ₁ Φ w (contragredient ρ₁ k ν : smoothVectors _) s = blockB μ₀ ρ₁ Φ w ν s
  simp only [blockB, contragredient_apply_apply]
  have hk1 : k.1 ∈ Ka := (Subgroup.mem_prod.1 hk).1
  simp_rw [rep_inv_mul_prod hw hk]
  rw [← integral_mul_right_eq_self _ k.1⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Units.val_mul, hΦ _ (inv_mem hk1)]
  rw [detPow_mul_of_mem_integralGL _ (hKa (inv_mem hk1)), _root_.mul_inv_rev, inv_inv,
    inv_mul_cancel_left]

end BlockDecomp

variable [MeasurableSpace F] [BorelSpace F]
  [∀ n : ℕ, MeasurableSpace (GL (Fin n) F)] [∀ n : ℕ, BorelSpace (GL (Fin n) F)]
  {W : Type w} [AddCommGroup W] [Module ℂ W]


variable (F W) in
def MultiFEStatement (ψ : AddChar F Circle) (r : ℕ) : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], Fintype.card ι = r →
  ∀ (d : ι → ℕ) [∀ i, NeZero (d i)] (μ : ∀ i, Measure (GL (Fin (d i)) F))
    [∀ i, (μ i).IsHaarMeasure]
    (H : Type (max u uF)) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (ρ : Representation ℂ ((∀ i, GL (Fin (d i)) F) × H) W), IsAdmissible ρ → ρ.IsIrreducible →
    ∀ α : ι → ℂ, (∀ i, α i ≠ 0) →
      (∀ i v, ρ (Pi.mulSingle i (centralUnif F (d i)), 1) v = α i • v) →
      (∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        ∃ C : Set (∀ i, GL (Fin (d i)) F), IsCompact C ∧
          ∀ x, ℓ (ρ (x, 1) v) ≠ 0 → ∃ j : ι → ℤ, (fun i => centralUnif F (d i) ^ j i) * x ∈ C) →
    ∃ γ : RatFunc ℂ, ∀ Ψ : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ,
      (∀ i, IsSchwartzBruhat (Ψ i)) → ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual ρ),
        RatFE F γ (fun s => ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ)
          (fun s => ∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x
            ∂Measure.pi μ)

theorem multiFEStatement_zero (ψ : AddChar F Circle) : MultiFEStatement.{uF, u, w} F W ψ 0 := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ ρ _ _ α _ _ _
  have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
  refine ⟨1, fun Ψ _ w ℓ _ => ?_⟩
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

theorem multiFEStatement_succ {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {r : ℕ}
    (ih : MultiFEStatement.{uF, u, w} F W ψ r) : MultiFEStatement.{uF, u, w} F W ψ (r + 1) := by
  intro ι _ _ hcard d _ μ _ H _ _ _ _ _ _ ρ hadm hirr α hα0 hα hsupp
  classical
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
  obtain ⟨γ', hIH⟩ := ih {i // i ≠ a} hcard' (fun j => d j) (fun j => μ j) (GL (Fin (d a)) F × H) ρ₂
    hadm₂ hirr₂ (fun j => α j) (fun j => hα0 j) hα₂ hsupp₂

  obtain ⟨s₀, hconv⟩ := exists_integrable_multi ρ hadm.1 hα0 hα hsupp μ
  obtain ⟨s₂, hconv₂⟩ := exists_integrable_multi ρ₂ hadm₂.1 (fun j => hα0 j) hα₂ hsupp₂
    (fun j => μ j)
  refine ⟨γa * γ', fun Ψ hΨ w ℓ hℓ => ?_⟩
  -- Keep the generated equations that the expansion proof first realized here.
  let _ := @multiA.eq_1.{uF, u, max u uF, w}
  let _ := @multiB.eq_1.{uF, u, max u uF, w}
  let _ := @GroundTheory.Automorphic.extendFixed.congr_simp.{max u uF, w}
  simpa only using block_mul_tail_FE hψ hψ1 hρ₁ hρ₂ hadm₁ hΨ hℓ
    ((hsm₁ ℓ).2 hℓ) ((hsm₂ ℓ).2 hℓ) hblock hIH hconv hconv₂
    (blockA_eq_sum (μ₀ := μ a) hadm₁.1) (blockB_eq_sum (μ₀ := μ a) hadm₁.1)

theorem multiFEStatement_all {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∀ r, MultiFEStatement.{uF, u, w} F W ψ r
  | 0 => multiFEStatement_zero ψ
  | r + 1 => multiFEStatement_succ hψ hψ1 (multiFEStatement_all hψ hψ1 r)

end GodementJacquet

end GroundTheory.Automorphic
