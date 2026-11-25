module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUnique
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.number_field_maps_local_ring_unique : ∀ (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B] [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B), π.comp s = π.comp t → s = t := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | exact GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq <;> assumption)
