module

public import Development.EtaleCohomology.EtaleSheaves.FibreEqvPf
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure.AicLoc

@[expose] public section

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.SpecAICPf

theorem aic_equiv {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A') (h : AIC A) : AIC A' := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _) (by rwa [natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have := congrArg e ha
  rw [eval_map, ← coe_eval₂RingHom, map_zero] at this
  rw [← this]

  simp [eval₂_eq_sum_range, eval_eq_sum_range, map_sum]

theorem card_roots_of_aic {A : Type} [CommRing A] [IsDomain A] (h : AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.Monic → p.natDegree = n → Multiset.card p.roots = n := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    rw [eq_one_of_monic_natDegree_zero hp hn]; simp
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    have e := mul_divByMonic_eq_iff_isRoot.2 ha
    have hq : (p /ₘ (X - C a)).Monic := Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [e]; exact hp)
    rw [← e, roots_mul (by rw [e]; exact hp.ne_zero), roots_X_sub_C, Multiset.card_add, ih _ hq hdeg]
    simp; omega

theorem aic_localization {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
    [IsLocalization M S] (h : AIC B) : AIC S := LateralTheory.E.BaseAICPf.Loc.aic_loc M h

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

theorem roots_eq {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] (hK : Function.Injective (algebraMap R K)) (L : Subalgebra R K) (hL : AIC L)
    (p : R[X]) (hp : p.Monic) : (p.map (algebraMap R L)).roots.map L.val.toRingHom = (p.map (algebraMap R K)).roots ∧
      Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
  have hinj : Function.Injective (algebraMap R L) := by
    intro a b hab
    exact hK (congrArg Subtype.val hab)
  have hc : Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
    rw [card_roots_of_aic hL _ _ (hp.map _) rfl, natDegree_map_eq_of_injective hinj]
  refine ⟨?_, hc⟩
  rw [roots_map_of_injective_of_card_eq_natDegree (f := L.val.toRingHom) Subtype.val_injective
    (by rw [hc, natDegree_map_eq_of_injective hinj]), map_map]
  rfl

theorem aic_of_local {R : Type} [CommRing R] [IsDomain R]
    (h : ∀ v : MaximalSpectrum R, AIC (Localization.AtPrime v.asIdeal)) : AIC R := by
  classical
  intro p hp hd
  let K := FractionRing R
  let L : MaximalSpectrum R → Subalgebra R K := fun v =>
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  have hL : ∀ v, AIC (L v) := fun v =>
    aic_equiv (IsLocalization.algEquiv v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal) (L v)).toRingEquiv (h v)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨e0, c0⟩ := roots_eq (IsFractionRing.injective R K) (L ⟨m, hm⟩) (hL _) p hp
  obtain ⟨x, hx⟩ : ∃ x, x ∈ (p.map (algebraMap R K)).roots := by
    rw [← e0]
    apply Multiset.exists_mem_of_ne_zero
    intro h0
    rw [Multiset.map_eq_zero] at h0
    rw [h0] at c0; simp at c0; omega
  have hmem : x ∈ (⊥ : Subalgebra R K) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot R K, Algebra.mem_iInf]
    intro v
    rw [← (roots_eq (IsFractionRing.injective R K) (L v) (hL v) p hp).1] at hx
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
    exact y.2
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.1 hmem
  refine ⟨a, ?_⟩
  have hr := (mem_roots (hp.map _).ne_zero).1 hx
  rw [IsRoot, eval_map, eval₂_hom] at hr
  exact (IsFractionRing.injective R K) (by rw [hr, map_zero])

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

open CategoryTheory AlgebraicGeometry

theorem stalk_aic (B : CommRingCat.{0}) (hA : AIC B) (x : Spec B) : AIC ((Spec B).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra B ((Spec B).presheaf.stalk x) := StructureSheaf.stalkAlgebra B x
  have : IsLocalization.AtPrime ((Spec B).presheaf.stalk x) x.asIdeal := StructureSheaf.IsLocalization.to_stalk B x
  exact aic_localization x.asIdeal.primeCompl hA

theorem SpecAIC_of : LateralTheory.E.FibreEqvPf.SpecAIC := by
  intro B hB hA
  refine ⟨inferInstance, ?_⟩
  intro U hU hne
  haveI : Nonempty U := hne.to_subtype
  apply aic_of_local
  intro v
  let y : PrimeSpectrum Γ(Spec B, U) := ⟨v.asIdeal, v.isMaximal.isPrime⟩
  have hy : hU.fromSpec y ∈ U := by
    show hU.fromSpec y ∈ (U : Set (Spec B))
    rw [← hU.range_fromSpec]; exact ⟨y, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk (Spec B).presheaf ⟨hU.fromSpec y, hy⟩
  have hloc : IsLocalization.AtPrime ((Spec B).presheaf.stalk (hU.fromSpec y)) y.asIdeal := hU.isLocalization_stalk' y hy
  have hst := stalk_aic B hA (hU.fromSpec y)
  exact aic_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl ((Spec B).presheaf.stalk (hU.fromSpec y))
    (Localization.AtPrime v.asIdeal)).toRingEquiv hst

end LateralTheory.E.SpecAICPf
