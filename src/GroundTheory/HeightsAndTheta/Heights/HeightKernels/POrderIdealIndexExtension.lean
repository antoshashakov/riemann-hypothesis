module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsOrderIdealIndexExtension
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PInvertibleIdealIndex
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace OrderIdealIndexExtensionAlt

theorem index_ne_zero_of_zsmul_mem {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] (H : AddSubgroup M)
    {N : ℤ} (hN : N ≠ 0) (h : ∀ x : M, N • x ∈ H) : H.index ≠ 0 := by
  have htor := (Module.isTorsionBy_quotient_iff H.toIntSubmodule N).2 h
  have : Finite (M ⧸ H) := Module.finite_of_fg_torsion (M ⧸ H.toIntSubmodule)
    (fun x => ⟨⟨N, mem_nonZeroDivisors_of_ne_zero hN⟩, @htor x⟩)
  exact AddSubgroup.index_ne_zero_of_finite

variable {L : Type} [Field L]

theorem exists_int_eq_mul [CharZero L] {B : Subring L} [Module.Finite ℤ B] {a : B} (ha : a ≠ 0) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ q : B, (c : B) = a * q := by
  let I : Ideal B := Ideal.span {a}
  have hI : I.under ℤ ≠ ⊥ :=
    I.under_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (IsIntegral.of_finite ℤ a)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact ⟨c, hc0, Ideal.mem_span_singleton.mp hc⟩

variable [NumberField L] {B : Subring L} [Module.Finite ℤ B]

theorem exists_family : ∃ S : Set (𝓞 L), S.Finite ∧ LinearIndepOn B (fun x : 𝓞 L => (x : L)) S ∧
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x : 𝓞 L,
      (N : L) * (x : L) ∈ Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) := by
  classical
  obtain ⟨S, hS, hmax⟩ := exists_maximal_linearIndepOn B (fun x : 𝓞 L => (x : L))
  set F := Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) with hF
  have hfin : S.Finite := by
    have h1 : LinearIndependent ℤ (fun x : S => ((x : 𝓞 L) : L)) := hS.restrict_scalars' ℤ
    have h2 : LinearIndependent ℤ (fun x : S => (x : 𝓞 L)) :=
      LinearIndependent.of_comp (algebraMap (𝓞 L) L).toIntAlgHom.toLinearMap h1
    exact Set.finite_coe_iff.mp h2.finite
  refine ⟨S, hfin, hS, ?_⟩
  have hone : ∀ x : 𝓞 L, ∃ c : ℤ, c ≠ 0 ∧ (c : L) * (x : L) ∈ F := by
    intro x
    by_cases hx : x ∈ S
    · exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span (Set.mem_image_of_mem _ hx)⟩
    · obtain ⟨a, ha, hax⟩ := hmax x hx
      obtain ⟨c, hc, q, hcq⟩ := exists_int_eq_mul ha
      refine ⟨c, hc, ?_⟩
      have h1 : (c : L) * (x : L) = q • (a • (x : L)) := by
        have h2 : (c : L) = ((c : B) : L) := by push_cast; rfl
        rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, h2, hcq]
        push_cast
        ring
      rw [h1]
      exact F.smul_mem q hax
  let P := (F.restrictScalars ℤ).comap (algebraMap (𝓞 L) L).toIntAlgHom.toLinearMap
  have htor : Module.IsTorsion ℤ (𝓞 L ⧸ P) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨c, hc0, hc⟩ := hone x
      refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      change (algebraMap (𝓞 L) L) (c • x) ∈ F
      rwa [map_zsmul, zsmul_eq_mul]
  obtain ⟨N, hN, hN0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htor
  refine ⟨N, nonZeroDivisors.coe_ne_zero ⟨N, hN0⟩, fun x => ?_⟩
  have hx := (Module.isTorsionBy_quotient_iff P N).mp
    (fun y => Submodule.mem_annihilator.mp hN y Submodule.mem_top) x
  change (algebraMap (𝓞 L) L) (N • x) ∈ F at hx
  rwa [map_zsmul, zsmul_eq_mul] at hx

end OrderIdealIndexExtensionAlt


open OrderIdealIndexExtensionAlt InvertibleIdealIndexAlt in
theorem OrderIdealIndexExtension.proof : OrderIdealIndexExtension.Statement := by
  intro L _ _ B hB
  classical
  have := hB
  obtain ⟨S, hSfin, hS, N, hN, hNF⟩ := exists_family (L := L) (B := B)
  have : Fintype S := hSfin.fintype
  set v : S → L := fun x => ((x : 𝓞 L) : L) with hv
  set φ : (S → B) →ₗ[B] L := Fintype.linearCombination B v with hφ
  have hφinj : Function.Injective φ :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp hS
  set Fs := Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) with hFs
  have hrange : ∀ y, y ∈ Fs ↔ ∃ β, φ β = y := by
    intro y
    rw [← LinearMap.mem_range, hφ, Fintype.range_linearCombination, hFs, Set.image_eq_range]
  set O := (1 : Submodule (𝓞 L) L).toAddSubgroup with hO
  set F := Fs.toAddSubgroup with hF
  have hmemO : ∀ x : 𝓞 L, (x : L) ∈ O := fun x => Submodule.mem_one.mpr ⟨x, rfl⟩
  have hOmem : ∀ y ∈ O, ∃ x : 𝓞 L, (x : L) = y := fun y hy => Submodule.mem_one.mp hy
  have hBF : ∀ b : B, ∀ y ∈ F, (b : L) * y ∈ F := fun b y hy => by
    have h1 := Fs.smul_mem b hy
    rwa [Subring.smul_def, smul_eq_mul] at h1
  have hFO : F ≤ O := by
    intro y hy
    obtain ⟨β, rfl⟩ := (hrange y).1 hy
    rw [hφ, Fintype.linearCombination_apply]
    refine O.sum_mem fun j _ => ?_
    rw [Subring.smul_def, smul_eq_mul]
    exact mul_mem_of_mem (β j).2 (hmemO _)
  have hNO : ∀ y ∈ O, (N : L) * y ∈ F := by
    intro y hy
    obtain ⟨x, rfl⟩ := hOmem y hy
    exact hNF x

  let toO := (algebraMap (𝓞 L) L).toAddMonoidHom.codRestrict O hmemO
  have htoO : Function.Surjective toO := by
    intro y
    obtain ⟨x, hx⟩ := hOmem y y.2
    exact ⟨x, Subtype.ext hx⟩
  have : Module.Finite ℤ O := Module.Finite.of_surjective toO.toIntLinearMap htoO
  have hFOidx : F.relIndex O ≠ 0 := by
    refine index_ne_zero_of_zsmul_mem (F.addSubgroupOf O) hN fun x => ?_
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_zsmul, zsmul_eq_mul]
    exact hNO x x.2

  have hint : ∀ β, IsIntegral ℤ (φ β) := fun β => by
    obtain ⟨x, hx⟩ := hOmem _ (hFO ((hrange _).2 ⟨β, rfl⟩))
    rw [← hx]
    exact x.isIntegral_coe
  let g1 : (S → B) →ₗ[ℤ] 𝓞 L :=
    (φ.restrictScalars ℤ).codRestrict (integralClosure ℤ L).toSubmodule hint
  have hg1 : Function.Injective g1 := fun a b h => hφinj (congrArg (fun x : 𝓞 L => (x : L)) h)
  let scale := (LinearMap.mulLeft ℤ (N : L)).comp (algebraMap (𝓞 L) L).toIntAlgHom.toLinearMap
  let g2 := scale.codRestrict ((LinearMap.range φ).restrictScalars ℤ)
    (fun x => (hrange _).1 (hNF x))
  have hg2 : Function.Injective g2 := fun x y h =>
    RingOfIntegers.ext (mul_left_cancel₀ (Int.cast_ne_zero.mpr hN) (congrArg Subtype.val h))
  have hr1 := LinearMap.finrank_le_finrank_of_injective hg1
  let e := (LinearEquiv.ofInjective φ hφinj).restrictScalars ℤ
  have hr2 := LinearMap.finrank_le_finrank_of_injective
    (f := e.symm.toLinearMap.comp g2) (e.symm.injective.comp hg2)
  have hrank : Module.finrank ℚ L = Fintype.card S * Module.finrank ℤ B := by
    rw [← RingOfIntegers.rank, le_antisymm hr2 hr1, Module.finrank_pi_fintype]
    simp
  refine ⟨Fintype.card S, (N : B), ?_, hrank, ?_, ?_⟩
  · intro h
    apply hN
    have h1 := congrArg (fun b : B => (b : L)) h
    simpa using h1
  · intro I hI
    obtain ⟨t, htI, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨c, hc, q, hcq⟩ := exists_int_eq_mul ht0
    refine index_ne_zero_of_zsmul_mem I.toAddSubgroup hc fun x => ?_
    rw [Submodule.mem_toAddSubgroup, zsmul_eq_mul, hcq, mul_assoc]
    exact I.mul_mem_right _ htI
  intro I hI hcase
  set J := (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup with hJ
  set IF := (AddSubgroup.pi Set.univ (fun _ : S => I.toAddSubgroup)).map φ.toAddMonoidHom with hIF
  have hmemIF : ∀ y, y ∈ IF ↔ ∃ β : S → B, (∀ j, β j ∈ I) ∧ φ β = y := by
    intro y
    simp [hIF, AddSubgroup.mem_pi]
  have hFtop : (⊤ : AddSubgroup (S → B)).map φ.toAddMonoidHom = F := by
    ext y
    simp [hF, hrange]
  have hIFidx : IF.relIndex F = I.toAddSubgroup.index ^ Fintype.card S := by
    rw [← hFtop, hIF, AddSubgroup.relIndex_map_map_of_injective _ _ hφinj,
      AddSubgroup.relIndex_top_right, AddSubgroup.index_pi]
    simp
  have hJO : J ≤ O := by
    intro y hy
    refine (Submodule.span_le.mpr ?_) hy
    rintro _ ⟨b, -, rfl⟩
    exact mem_one_of_mem b.2
  have hIF_I : ∀ i ∈ I, ∀ y ∈ F, (i : L) * y ∈ IF := by
    intro i hi y hy
    obtain ⟨β, rfl⟩ := (hrange y).1 hy
    refine (hmemIF _).2 ⟨i • β, fun j => ?_, ?_⟩
    · simpa using I.mul_mem_right (β j) hi
    · rw [map_smul, Subring.smul_def, smul_eq_mul]
  have hB_IF : ∀ b : B, ∀ y ∈ IF, (b : L) * y ∈ IF := by
    intro b y hy
    obtain ⟨β, hβ, rfl⟩ := (hmemIF y).1 hy
    refine (hmemIF _).2 ⟨b • β, fun j => ?_, ?_⟩
    · simpa using I.mul_mem_left b (hβ j)
    · rw [map_smul, Subring.smul_def, smul_eq_mul]
  have hIF_F : IF ≤ F := by
    intro y hy
    obtain ⟨β, -, rfl⟩ := (hmemIF y).1 hy
    exact (hrange _).2 ⟨β, rfl⟩
  have hIF_J : IF ≤ J := by
    intro y hy
    obtain ⟨β, hβ, rfl⟩ := (hmemIF y).1 hy
    rw [hφ, Fintype.linearCombination_apply]
    refine J.sum_mem fun j _ => ?_
    have h1 : β j • v j = (j : 𝓞 L) • ((β j : B) : L) := by
      rw [Subring.smul_def, smul_eq_mul, Algebra.smul_def, mul_comm]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨β j, hβ j, rfl⟩)
  rcases hcase with hP | hcop
  ·
    obtain ⟨t, hIt⟩ : ∃ t : B, I = Ideal.span {t} :=
      ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
    have ht0 : (t : L) ≠ 0 := by
      intro h
      apply hI
      rw [hIt, Ideal.span_singleton_eq_bot]
      exact Subtype.ext h
    have hJt : J = O.map (mulBy (t : L)) := by
      rw [hJ, hIt, ← map_mul_eq_span t]
    have hIFt : IF = F.map (mulBy (t : L)) := by
      ext y
      rw [hmemIF]
      constructor
      · rintro ⟨β, hβ, rfl⟩
        have h1 : ∀ j, ∃ a : B, a * t = β j := fun j => by
          have := hβ j
          rw [hIt] at this
          exact Ideal.mem_span_singleton'.mp this
        choose a ha using h1
        refine ⟨φ a, (hrange _).2 ⟨a, rfl⟩, ?_⟩
        have h2 : β = t • a := funext fun j => by simp [← ha j, mul_comm]
        rw [h2, mulBy_apply, map_smul, Subring.smul_def, smul_eq_mul]
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨a, rfl⟩ := (hrange z).1 hz
        refine ⟨t • a, fun j => ?_, ?_⟩
        · rw [hIt]
          simpa using Ideal.mul_mem_right (a j) _ (Ideal.mem_span_singleton_self t)
        · rw [mulBy_apply, map_smul, Subring.smul_def, smul_eq_mul]
    have hFt : F.map (mulBy (t : L)) ≤ F := by
      rintro _ ⟨z, hz, rfl⟩
      exact hBF t z hz
    have hOt : O.map (mulBy (t : L)) ≤ O := by
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem_of_mem t.2 hz
    have e1 : (F.map (mulBy (t : L))).relIndex (O.map (mulBy (t : L))) = F.relIndex O :=
      AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective ht0)
    have h1 := (AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hFO) hOt).trans
      (AddSubgroup.relIndex_mul_relIndex _ _ _ hFt hFO).symm
    rw [e1, mul_comm (AddSubgroup.relIndex _ F)] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hFOidx) h1
    rw [hJt, h2, ← hIFt, hIFidx]
  ·
    have h1 : (1 : B) ∈ I ⊔ Ideal.span {(N : B)} := hcop ▸ Submodule.mem_top
    obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hib : (i : L) + (b : L) * (N : L) = 1 := by
      have := congrArg (fun x : B => (x : L)) hiz
      simpa using this
    have key (y : L) (hy : y ∈ J) : (N : L) * y ∈ IF := by
      change y ∈ Submodule.span (𝓞 L) ((fun j : B => (j : L)) '' (I : Set B)) at hy
      rw [Set.image_eq_range] at hy
      obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
      simp only [Finsupp.sum, Finset.mul_sum]
      refine IF.sum_mem fun j _ => ?_
      rw [Algebra.smul_def, show (N : L) * ((c j : L) * ((j : B) : L)) =
        ((j : B) : L) * ((N : L) * (c j : L)) by ring]
      exact hIF_I j j.2 _ (hNF (c j))
    have hsup : J ⊔ F = O := by
      refine le_antisymm (sup_le hJO hFO) fun x hx => ?_
      obtain ⟨o, rfl⟩ := hOmem x hx
      have h2 : (o : L) = (i : L) * (o : L) + (b : L) * ((N : L) * (o : L)) := by
        linear_combination (-(o : L)) * hib
      rw [h2]
      refine AddSubgroup.add_mem_sup ?_ (hBF b _ (hNO _ hx))
      have h3 : (i : L) * (o : L) = o • (i : L) := by
        rw [Algebra.smul_def, mul_comm]
      rw [h3]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    have hinf : J ⊓ F = IF := by
      refine le_antisymm (fun y hy => ?_) (le_inf hIF_J hIF_F)
      have h2 : y = (i : L) * y + (b : L) * ((N : L) * y) := by
        linear_combination (-y) * hib
      rw [h2]
      refine IF.add_mem (hIF_I i hi y hy.2) (hB_IF b _ ?_)
      exact key y hy.1
    calc J.relIndex O = J.relIndex (J ⊔ F) := by rw [hsup]
      _ = J.relIndex F := AddSubgroup.relIndex_sup_left _ _
      _ = (J ⊓ F).relIndex F := (AddSubgroup.inf_relIndex_right _ _).symm
      _ = IF.relIndex F := by rw [hinf]
      _ = _ := hIFidx

end

end GroundTheory.Heights₂.Heights
