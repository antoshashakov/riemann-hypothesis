module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisibleOrdinarySelmerChainExistsIntegralRepres
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleLocalConditions
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDivisibleChainPrimaryTorsionGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteLTorsionSelmerRankTwoAdjoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualExistsNoEigenvalueOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNorma
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualUpperTriangularDecomposi
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroOrdinaryClassOfCompatibleCocyclesModPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem gw_limit : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  intro hL l _ Ω _ _ _ e S A W hW c hc H hGr
  have h1 := _root_.GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual l Ω e S A W hW
  have h2 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm l Ω e S A W hW c hc
  have h3 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt l Ω e S A W hW
  have h4 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified l Ω e S A W hW
  have h5 := _root_.GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup l Ω e S A W hW
  have hunb := _root_.GlobalTheory.Ord2.Unbounded.divSel_unbounded l Ω S A (dual1 W) c h2 h3 H
  have hfin := _root_.GlobalTheory.Ord2.finite_lTorsion_divSel hL l Ω S A (dual1 W) c hW.above h1 h2 h4
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.Ord2.DivChain.exists_divisible_chain l (DivSel c (dual1 W) S A) (divSel_torsion c (dual1 W) S A) hfin hunb
  obtain ⟨a, N, p1, p2, p3, p4, p5, p6, p7, p8⟩ := _root_.GlobalTheory.Ord2.DivChain.representatives l Ω S A (dual1 W) c h1 h2 h4 h5 x hx0 hx
  exact _root_.GlobalTheory.Ord2.limit_nonzero_ordinary_class l Ω S A (dual1 W) c h1 h2 h3 a N p1 p2 p3 p4 p5 p6 p7 p8 hGr

end GlobalTheory.Ord2

end
