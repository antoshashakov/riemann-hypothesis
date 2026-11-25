module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeet
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A, σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  first | exact @GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | exact GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | (intros; apply GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine <;> assumption)
