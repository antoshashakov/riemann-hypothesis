module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsInvertibleIdealIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsOrderIdealIndexExtension
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLocallyPrincipalCoprime
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ExistsSmulMemOfSpanEqTop
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
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
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace InvertibleIdealIndexAlt

variable {L : Type} [Field L]

def mulBy (c : L) : L →+ L := AddMonoidHom.mulLeft c

@[simp] theorem mulBy_apply (c x : L) : mulBy c x = c * x := rfl

theorem mulBy_injective {c : L} (hc : c ≠ 0) : Function.Injective (mulBy c) :=
  fun _ _ h => mul_left_cancel₀ hc h

theorem genIndex_eq {X J M : AddSubgroup L} {β δ : L} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hJX : J ≤ X)
    (hβX : X.map (mulBy β) ≤ X) (hδX : X.map (mulBy δ) ≤ X) (hβJ : J.map (mulBy β) ≤ J)
    (hM : ∀ x, x ∈ M ↔ ∃ y ∈ J, β * x = δ * y) (hJ : J.relIndex X ≠ 0)
    (hδ' : (X.map (mulBy δ)).relIndex X ≠ 0) :
    genIndex M X = ((X.map (mulBy β)).relIndex X : ℝ) /
      (((X.map (mulBy δ)).relIndex X : ℝ) * (J.relIndex X : ℝ)) := by
  have hMβ : M.map (mulBy β) = J.map (mulBy δ) := by
    ext z
    simp only [AddSubgroup.mem_map, mulBy_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, h⟩ := (hM x).1 hx
      exact ⟨y, hy, h.symm⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨δ * y / β, (hM _).2 ⟨y, hy, by field_simp⟩, by field_simp⟩
  let A := J.map (mulBy δ)
  let B := X.map (mulBy β)
  have hAX : A ≤ X := (AddSubgroup.map_mono hJX).trans hδX
  have hAidx : A.relIndex X = J.relIndex X * (X.map (mulBy δ)).relIndex X := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hJX) hδX,
      AddSubgroup.relIndex_map_map_of_injective (f := mulBy δ) _ _ (mulBy_injective hδ)]
  have hAn : A.relIndex X ≠ 0 := hAidx.symm ▸ mul_ne_zero hJ hδ'
  have hABn : A.relIndex B ≠ 0 := mt (AddSubgroup.relIndex_eq_zero_of_le_right hβX) hAn
  have hrel : B.relIndex A * A.relIndex X = A.relIndex B * B.relIndex X := by
    rw [← AddSubgroup.inf_relIndex_left A B, ← AddSubgroup.inf_relIndex_right A B,
      AddSubgroup.relIndex_mul_relIndex _ _ _ inf_le_left hAX,
      AddSubgroup.relIndex_mul_relIndex _ _ _ inf_le_right hβX]
  rw [← KLinesLineDegree.genIndex_map_of_injective (mulBy β) (mulBy_injective hβ), hMβ]
  change (B.relIndex A : ℝ) / (A.relIndex B : ℝ) =
    (B.relIndex X : ℝ) / ((X.map (mulBy δ)).relIndex X * (J.relIndex X : ℝ))
  rw [mul_comm, ← Nat.cast_mul, ← hAidx]
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr hABn) (Nat.cast_ne_zero.mpr hAn)).2
  exact_mod_cast hrel.trans (Nat.mul_comm _ _)

theorem isIntegral_of_mem {B : Subring L} [Module.Finite ℤ B] {b : L} (hb : b ∈ B) :
    IsIntegral ℤ b :=
  (IsIntegral.of_finite ℤ (⟨b, hb⟩ : B)).map (B.subtype.toIntAlgHom)

theorem mul_mem_of_mem [NumberField L] {B : Subring L} [Module.Finite ℤ B] {S : Submodule (𝓞 L) L} {b z : L}
    (hb : b ∈ B) (hz : z ∈ S) : b * z ∈ S := by
  exact S.smul_mem (⟨b, isIntegral_of_mem hb⟩ : 𝓞 L) hz

theorem mem_one_of_mem [NumberField L] {B : Subring L} [Module.Finite ℤ B] {b : L} (hb : b ∈ B) :
    b ∈ (1 : Submodule (𝓞 L) L) := by
  have h := mul_mem_of_mem (S := 1) hb (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  rwa [mul_one] at h

theorem mem_span_of_local [NumberField L] {B : Subring L} [Module.Finite ℤ B] {M : AddSubgroup L} {ι : Type}
    {a : ι → L}
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    {z : L} (hz : z ∈ M) : z ∈ Submodule.span (𝓞 L) (Set.range a) := by
  let f : B →+* 𝓞 L := B.subtype.codRestrict (integralClosure ℤ L).toSubring
    (fun b => isIntegral_of_mem b.2)
  let _ : Algebra B (𝓞 L) := f.toAlgebra
  let _ : IsScalarTower B (𝓞 L) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := Submodule.span (𝓞 L) (Set.range a)
  let J : Ideal B := (S.restrictScalars B).comap (LinearMap.toSpanSingleton B L z)
  by_contra hzS
  have hJ : J ≠ ⊤ := fun h => hzS (by
    have h1 : (1 : B) ∈ J := h ▸ Submodule.mem_top
    simpa [J, LinearMap.toSpanSingleton_apply_one] using h1)
  obtain ⟨m, hm, hJm⟩ := J.exists_le_maximal hJ
  obtain ⟨i, hi⟩ := hloc m hm
  obtain ⟨b, c, hbm, hbc⟩ := hi z hz
  apply hbm (hJm ?_)
  change (b : L) * z ∈ S
  rw [hbc]
  exact mul_mem_of_mem c.2 (Submodule.subset_span ⟨i, rfl⟩)

theorem relIndex_map_subtype (B : Subring L) (H : AddSubgroup B) :
    (H.map B.subtype.toAddMonoidHom).relIndex B.toAddSubgroup = H.index := by
  have hinj : Function.Injective B.subtype.toAddMonoidHom := Subtype.val_injective
  have hr : (⊤ : AddSubgroup B).map B.subtype.toAddMonoidHom = B.toAddSubgroup := by
    ext x
    simp
  rw [← hr, ← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq_self_of_injective hinj,
    AddSubgroup.relIndex_top_right]

theorem map_mul_eq (B : Subring L) (β : B) :
    B.toAddSubgroup.map (mulBy (β : L)) =
      (Ideal.span {β}).toAddSubgroup.map B.subtype.toAddMonoidHom := by
  ext x
  simp only [AddSubgroup.mem_map, mulBy_apply, Submodule.mem_toAddSubgroup,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩ * β, ⟨⟨y, hy⟩, rfl⟩, by simp [mul_comm]⟩
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, c.2, by simp [mul_comm]⟩

theorem map_mul_eq_span [NumberField L] {B : Subring L} [Module.Finite ℤ B] (β : B) :
    (1 : Submodule (𝓞 L) L).toAddSubgroup.map (mulBy (β : L)) =
      (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' ((Ideal.span {β} : Ideal B) : Set B))).toAddSubgroup := by
  let f : B →+* 𝓞 L := B.subtype.codRestrict (integralClosure ℤ L).toSubring
    (fun b => isIntegral_of_mem b.2)
  let incl := Algebra.linearMap (𝓞 L) L
  change ((1 : Submodule (𝓞 L) L).map (LinearMap.mulLeft (𝓞 L) (β : L))).toAddSubgroup =
    (Submodule.span (𝓞 L) ((fun b => incl (f b)) '' ((Ideal.span {β} : Ideal B) : Set B))).toAddSubgroup
  rw [Submodule.one_eq_span, Submodule.map_span, Set.image_singleton, ← Set.image_image incl f]
  rw [← Submodule.map_span]
  change (Submodule.span (𝓞 L) {_}).toAddSubgroup =
    (Submodule.map incl (Ideal.map f (Ideal.span {β}))).toAddSubgroup
  rw [Ideal.map_span, Set.image_singleton, Submodule.map_span, Set.image_singleton]
  simp only [LinearMap.mulLeft_apply, mul_one]
  rfl

theorem card_one_eq_zero [NumberField L] : Nat.card (1 : Submodule (𝓞 L) L).toAddSubgroup = 0 := by
  have : Infinite (1 : Submodule (𝓞 L) L).toAddSubgroup :=
    Infinite.of_injective (fun n : ℕ => (⟨(n : L), Submodule.mem_one.mpr ⟨n, by simp⟩⟩ :
      (1 : Submodule (𝓞 L) L).toAddSubgroup))
      (fun m n h => Nat.cast_injective (R := L) (congrArg Subtype.val h))
  exact Nat.card_eq_zero_of_infinite

theorem card_subring_eq_zero [NumberField L] (B : Subring L) : Nat.card B.toAddSubgroup = 0 := by
  have : Infinite B.toAddSubgroup :=
    Infinite.of_injective (fun n : ℕ => (⟨(n : L), by simp⟩ : B.toAddSubgroup))
      (fun m n h => Nat.cast_injective (R := L) (congrArg Subtype.val h))
  exact Nat.card_eq_zero_of_infinite

end InvertibleIdealIndexAlt


open InvertibleIdealIndexAlt in
theorem InvertibleIdealIndex.proof (h1 : OrderIdealIndexExtension.Statement)
    (h2 : LocallyPrincipalCoprime.Statement) : InvertibleIdealIndex.Statement := by
  intro L _ _ B M ι _ a hB hBM haM hden hloc
  have := hB
  by_cases hM0 : M = ⊥
  · have ha0 : ∀ i, a i = 0 := fun i => by simpa [hM0] using haM i
    have hT0 : Submodule.span (𝓞 L) (Set.range a) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      exact ha0 i
    simp only [hM0, hT0, Submodule.bot_toAddSubgroup, genIndex, AddSubgroup.relIndex_bot_left,
      AddSubgroup.relIndex_bot_right, card_subring_eq_zero, card_one_eq_zero]
    simp
  obtain ⟨r, s, hs, hrank, hfin, hidx⟩ := h1 L B hB
  obtain ⟨β, δ, I, hβ, hδ, hIs, hMI⟩ := h2 L B M ι a hB hBM haM hden hloc hM0 s hs
  have hβL : (β : L) ≠ 0 := fun h => hβ (Subtype.ext h)
  have hδL : (δ : L) ≠ 0 := fun h => hδ (Subtype.ext h)
  have hI0 : I ≠ ⊥ := by
    intro hI
    obtain ⟨⟨x, hxM⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hM0
    obtain ⟨y, hy, hxy⟩ := (hMI x).1 hxM
    rw [hI, Ideal.mem_bot] at hy
    subst hy
    have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    simp [hβL, hx] at hxy
  have hspanβ : Ideal.span {β} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hβ
  have hspanδ : Ideal.span {δ} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hδ

  have g1 := genIndex_eq (X := B.toAddSubgroup) (J := I.toAddSubgroup.map B.subtype.toAddMonoidHom)
    (M := M) hβL hδL
    (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem δ.2 hy)
    (by rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨β * y, I.mul_mem_left β hy, rfl⟩)
    (by
      intro x
      rw [hMI x]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨y, ⟨y, hy, rfl⟩, h⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
        exact ⟨y, hy, h⟩)
    (by rw [relIndex_map_subtype]; exact hfin I hI0)
    (by rw [map_mul_eq, relIndex_map_subtype]; exact hfin _ hspanδ)
  rw [map_mul_eq, map_mul_eq, relIndex_map_subtype, relIndex_map_subtype, relIndex_map_subtype]
    at g1

  have hJ2 : Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B)) ≤ 1 :=
    Submodule.span_le.mpr (by rintro _ ⟨y, _, rfl⟩; exact mem_one_of_mem y.2)
  have hTJ : (Submodule.span (𝓞 L) (Set.range a)).map (LinearMap.mulLeft (𝓞 L) (β : L)) =
      (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).map
        (LinearMap.mulLeft (𝓞 L) (δ : L)) := by
    apply le_antisymm
    · rw [Submodule.map_span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨y, hy, h⟩ := (hMI (a i)).1 (haM i)
      exact ⟨y, Submodule.subset_span ⟨y, hy, rfl⟩, h.symm⟩
    · rw [Submodule.map_span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hx : (δ : L) * y / β ∈ M := (hMI _).2 ⟨y, hy, by field_simp⟩
      exact ⟨_, mem_span_of_local hloc hx,
        show (β : L) * ((δ : L) * y / β) = (δ : L) * y by field_simp⟩
  have g2 := genIndex_eq (X := (1 : Submodule (𝓞 L) L).toAddSubgroup)
    (J := (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup)
    (M := (Submodule.span (𝓞 L) (Set.range a)).toAddSubgroup) hβL hδL
    (fun x hx => hJ2 hx)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem δ.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact mul_mem_of_mem β.2 hy)
    (by
      intro x
      have hinj : Function.Injective (LinearMap.mulLeft (𝓞 L) (β : L)) := mulBy_injective hβL
      simp only [Submodule.mem_toAddSubgroup]
      rw [← Submodule.comap_map_eq_of_injective hinj (Submodule.span (𝓞 L) (Set.range a)), hTJ]
      simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mulLeft_apply, eq_comm])
    (by rw [hidx I hI0 (Or.inr hIs)]; exact pow_ne_zero _ (hfin I hI0))
    (by
      rw [map_mul_eq_span δ, hidx _ hspanδ (Or.inl ⟨⟨δ, rfl⟩⟩)]
      exact pow_ne_zero _ (hfin _ hspanδ))
  rw [map_mul_eq_span β, map_mul_eq_span δ, hidx _ hspanβ (Or.inl ⟨⟨β, rfl⟩⟩),
    hidx _ hspanδ (Or.inl ⟨⟨δ, rfl⟩⟩), hidx I hI0 (Or.inr hIs)] at g2
  rw [g1, g2, hrank]
  push_cast
  rw [← mul_pow, ← div_pow, Real.log_pow]
  ring

end

end GroundTheory.Heights₂.Heights
