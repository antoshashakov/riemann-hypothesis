module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetEmptyPlacesLattice
import Supplements.MathlibImports.AnalysisAndTactics
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

theorem _root_.GlobalTheory.T.coset_empty_places_lattice : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (I : Ideal (𝓞 F)) (x0 : ι → F), cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | exact GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | (intros; apply GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset <;> assumption)
