module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFramesAwayPrime
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.lattice_frames_away_prime : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (I : Type) [Fintype I] (r : I → ℕ) (Vg : I → Submodule Ω Li) (V W : I → Lat ξ Li) (p : ℕ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → p.Prime → (∀ i, (V i).IsVB (r i) (Vg i)) → (∀ i, (W i).IsVBOn {q | ∀ l : ℕ, l.Prime → l ≠ p → ¬ InFibre ξ l q} (r i) (Vg i)) → (∀ i (q : Cpt ξ), Char0 ξ q → W i q = V i q) → ∃ Δ : Lat ξ Ω, Δ.IsVB 1 ⊤ ∧ (∀ q, ¬ InFibre ξ p q → Δ q = Submodule.span (regAt ξ q) {1}) ∧ ∀ q, InFibre ξ p q → ∀ (b b' : ∀ i, Fin (r i) → Li) (T : ∀ i, Matrix (Fin (r i)) (Fin (r i)) Ω), (∀ i, (V i).IsFrameAt (b i) q) → (∀ i, (W i).IsFrameAt (b' i) q) → (∀ i k, b' i k = ∑ k', T i k' k • b i k') → Δ q = Submodule.span (regAt ξ q) {∏ i, (T i).det} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine.exists_delta | exact GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine.exists_delta | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoModel.DeltaLine.exists_delta <;> assumption)
