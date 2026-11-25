module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeterminantIdentities
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiDet :
    ∀ {n : ℕ} {B A H G : Type} [CommRing B] [CommRing A] [Group H] [Group G] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace G] (I : Ideal B) [IsHausdorff I B] (f : B →+* A), Function.Injective f → ∀ (π : H →* G), Function.Surjective π → Topology.IsQuotientMap π → ∀ (ρ : H →* Matrix (Fin n) (Fin n) A) (cp : H → B[X]), (∀ g, (cp g).map f = (ρ g).charpoly) → (∀ j, AdicCont I fun g => (cp g).coeff j) → (∀ U : Subgroup H, IsClosed (U : Set H) → ρ.ker ≤ U → π.ker ≤ U) → ∃ D : W.GDet n B G, (D.comap π).map f = W.GDet.ofRep ρ ∧ (∀ g, D.chi (MonoidAlgebra.single (π g) 1) = cp g) ∧ D.IsCont I :=
  _root_.UpperTheory.Reformulated.B.DeterminantIdentities.phiDet
