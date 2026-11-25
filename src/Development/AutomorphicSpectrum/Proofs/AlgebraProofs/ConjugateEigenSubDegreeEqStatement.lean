module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEigenSubDegreeEq
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.conjugate_eigen_sub_degree_eq : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ s t : S, (∀ a, χ t a = χ s (star a)) → subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) = subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj | exact GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj <;> assumption)
