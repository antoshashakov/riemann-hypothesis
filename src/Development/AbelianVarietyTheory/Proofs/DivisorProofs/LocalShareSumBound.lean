module

public import Formalism.LocalToGlobal.GlobalTheory.ConcNWeight
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
public import Formalism.LocalToGlobal.GlobalTheory.ConcNP
import Formalism.PadicSubsetSums.StableGradedCounts.DominantNumbersEighthOfSharp
import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight
import Formalism.PadicSubsetSums.StableGradedCounts.PropertyWOfEstimates
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkIRROfJoinEx

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.LocShareNum

open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW host_facts sum_wtOf eUk_coeff_one_re_pos eJk_coeff_one_re_pos wtOf_eq_zero_of_not_label rangeW_of_sizes)

local instance factG {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem tieAdmG_rec (D : D7) : TieAdmG D := fun k =>
  ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩



theorem locShare_eUk_le_Wg {D : D7} (hL : admLq D) (hA : TieAdmG D) (hR : RangeW D)
    (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ : ∀ k, ψ₀ k ≠ 1)
    (k : Fin 2) (S : Finset (Formalism.MainNotions.ArithmeticCylinders.Tup D k)) (hS : ∀ t ∈ S, ¬ goodAt D k t) :
    locShare D (fun k _ => eUk D k (ψ₀ k)) k S ≤ Wg D.R.f D.R.m D.R.r (D.host.g k) D.host.q D.host.d := by
  classical
  let eV : VecAt D := fun k _ => eUk D k (ψ₀ k)
  have hv : ∀ (k : Fin 2) (v : D.nd.PlG k), eV k v = eUk D k (ψ₀ k) ∨ eV k v = eJk D k (ψ₀ k) :=
    fun _ _ => Or.inl rfl
  show locShare D eV k S ≤ _
  obtain ⟨hnn, hsq, hcmp, -⟩ := hL k (ψ₀ k) (hψ k)
  obtain ⟨hq, hd, hqd, hq2, hd2, h16m, h16, hqg, hdg⟩ := host_facts hA k
  let wJ : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) → ℝ :=
    fun v c => Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (Formalism.CyclotomicNorms.monicOf c)
  let P : (Fin D.R.r → ZMod (D.host.g k)) → ℝ := fun c => Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c)
  have hJnn : ∀ v f, 0 ≤ Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) f := by
    intro v f
    rcases hv k v with h | h <;> rw [h]
    · exact (hnn f).1
    · exact (hnn f).2
  have hPnn : ∀ c, 0 ≤ P c := fun c => (hnn _).1
  have hJsum : ∀ v, ∑ c, wJ v c = 1 := by
    intro v
    rcases hv k v with h | h
    · simp only [wJ]; rw [h]; exact sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'
    · simp only [wJ]; rw [h]; exact sum_wtOf k _ (eJk_coeff_one_re_pos k _).ne'
  have hPsum : ∑ c, P c = 1 := sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'
  have hg1 : (1 : ℝ) ≤ (D.host.g k : ℝ) := by exact_mod_cast (D.host.g_prime k).one_lt.le
  have hcmpv : ∀ v c, (1 - 1 / (D.host.g k : ℝ)) * P c ≤ wJ v c := by
    intro v c
    have hle : 1 - 1 / (D.host.g k : ℝ) ≤ 1 := sub_le_self _ (by positivity)
    rcases hv k v with h | h
    · have : wJ v c = P c := by simp only [wJ, P]; rw [h]
      rw [this]
      exact mul_le_of_le_one_left (hPnn c) hle
    · have : wJ v c = Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eJk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c) := by simp only [wJ]; rw [h]
      rw [this]
      by_cases hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c)
      · exact hcmp _ hlab
      · simp only [P]
        rw [wtOf_eq_zero_of_not_label _ hlab, wtOf_eq_zero_of_not_label _ hlab, mul_zero]
  have hred : locShare D eV k S ≤
      ∑ x ∈ (Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter
        (fun x => ¬ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) D.R.r
          (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (x v)) (D.nd.chiT k)), ∏ v, wJ v (x v) := by
    unfold locShare
    let cv : Formalism.MainNotions.ArithmeticCylinders.Tup D k → (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k)) := fun t v i => (t v).coeff i
    have hS' : ∑ t ∈ S, ∏ v, Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (t v) =
        ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (t v) := by
      rw [Finset.sum_filter_of_ne]
      intro t _ hne v
      by_contra hv'
      exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (wtOf_eq_zero_of_not_label _ hv'))
    have hcv : ∀ t : Formalism.MainNotions.ArithmeticCylinders.Tup D k, (∀ v, IsLabel D k (t v)) → ∀ v, Formalism.CyclotomicNorms.monicOf (cv t v) = t v :=
      fun t ht v => Formalism.CyclotomicNorms.Sqf.monicOf_coeffs (t v) (ht v).1 (ht v).2.1
    rw [hS']
    calc ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eV k v) (t v)
        = ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, wJ v (cv t v) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          have ht := (Finset.mem_filter.1 ht).2
          refine Finset.prod_congr rfl fun v _ => ?_
          simp only [wJ]
          rw [hcv t ht v]
      _ = ∑ x ∈ (S.filter (fun t => ∀ v, IsLabel D k (t v))).image cv, ∏ v, wJ v (x v) := by
          rw [Finset.sum_image]
          intro t ht t' ht' h
          have ht := (Finset.mem_filter.1 ht).2
          have ht' := (Finset.mem_filter.1 ht').2
          funext v
          rw [← hcv t ht v, ← hcv t' ht' v]
          exact congrArg Formalism.CyclotomicNorms.monicOf (congrFun h v)
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun x _ _ => Finset.prod_nonneg fun v _ => hJnn v _
          intro x hx
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨htS, htl⟩ := Finset.mem_filter.1 ht
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hgood => hS t htS ?_⟩
          have hfun : (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (cv t v)) = t := funext fun v => hcv t htl v
          rw [hfun] at hgood
          exact Formalism.MainNotions.N.PlaceLabelTeichmuller.good_of D.R.r t (D.nd.chiT k) hgood
  have hT := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.comparison_transfer_holds (D.nd.PlG k) (fun _ => Fin D.R.r → ZMod (D.host.g k))
    (fun _ => P) wJ (D.host.g k : ℝ)
    ((Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter
        (fun x => ¬ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) D.R.r
          (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (x v)) (D.nd.chiT k)))
    hg1 (fun _ => hPnn) (fun _ => hPsum) hJsum hcmpv
  have hW := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.property_W_of_estimates (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (D.nd.PlG k)
    (Fin D.R.m) D.R.r D.host.q D.host.d (D.nd.chiT k) P hR.1 (by rw [ZMod.card]; exact hR.2 k) hq hd hqd hq2
    hd2 h16m (by rw [ZMod.card]; exact h16) (by rw [ZMod.card]; exact hqg) (by rw [ZMod.card]; exact hdg)
    hPnn hPsum (by
      intro c hc
      have hc' : c ∈ (Finset.univ : Finset (Fin D.R.r → ZMod (D.host.g k))).filter
          (fun c => Squarefree (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).coeff 0 ≠ 0) := by
        unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqSet at hc
        convert hc
      obtain ⟨-, hsqf, h0⟩ := Finset.mem_filter.1 hc'
      have hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c) :=
        ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf c, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf c, h0⟩
      show Formalism.MainNotions.ArithmeticCylinders.wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c) = _
      rw [hsq _ hlab hsqf, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight, ZMod.card, one_div, ← Multiset.prod_map_inv]
      convert rfl <;> rfl)
  refine le_trans hred (le_trans hT ?_)
  refine le_trans (add_le_add hW le_rfl) (le_of_eq ?_)
  rw [ZMod.card, D.nd.card_PlG k, Fintype.card_fin]
  unfold Wg
  ring



theorem sizesRec_at_point {eps : ℝ} (Fm : FamP eps) {x : ℝ} (hx : Fm.x1 < x) (hx4 : 4 ≤ x) (i : Fm.Ix x) {Cs : ℝ}
    (hCs : 6 ≤ Cs) : SizesRec (Fm.D x i) x Fm.ez Cs := by
  first
  | exact _root_.GlobalTheory.Top.Irr.sizesRec_at
  | (apply _root_.GlobalTheory.Top.Irr.sizesRec_at <;> assumption)

end GlobalTheory.CovTop.LocShareNum

namespace GlobalTheory.CovTop.LocShareNum

open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW rangeW_of_sizes)

theorem stdAddChar_ne_one (D : D7) (k : Fin 2) :
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) ≠ 1 := by
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have h := ZMod.isPrimitive_stdAddChar (D.host.g k) (one_ne_zero : (1 : ZMod (D.host.g k)) ≠ 0)
  rwa [AddChar.mulShift_one] at h

theorem wg_sum_le (eps : ℝ) (he : 0 < eps) (he1 : eps ≤ 1) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ D : D7, SizesRec D x eps 6 →
      Wg D.R.f D.R.m D.R.r (D.host.g 0) D.host.q D.host.d + Wg D.R.f D.R.m D.R.r (D.host.g 1) D.host.q D.host.d
        ≤ Real.exp (-(x ^ (eps / 7))) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (weight_numbers_bound eps 6 he he1)
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds (3 * 6 + 3) eps he)
  refine ⟨max a b, fun x hx D hS => ?_⟩
  have h0 := ha x (le_trans (le_max_left _ _) hx) _ _ _ _ _ _ (hS 0)
  have h1 := ha x (le_trans (le_max_left _ _) hx) _ _ _ _ _ _ (hS 1)
  have h2 := hb x (le_trans (le_max_right _ _) hx)
  have hE : 0 ≤ Real.exp (-(x ^ (eps / 7))) := (Real.exp_pos _).le
  linarith

end GlobalTheory.CovTop.LocShareNum
