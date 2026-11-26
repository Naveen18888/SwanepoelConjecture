module
public import Swanepoel.L38PentagonBankBins
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.isolated_pentagon_pair_crossings_le_three_of_bins
    {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    {F H : PlaneFace G} (P : PentagonFaceBoundary G F) (Q : PentagonFaceBoundary G H)
    (hFY : F∈Y) (hHY : H∈Y) (hne : H≠F)
    (hFports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (hHports : ∀ s∈G.faceSourcePorts H,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    {ρ : ℝ} (D : P.BankBinData ρ) (E : Q.BankBinData ρ) :
    G.interFamilyCrossings ht {F} {H}≤3 := by
  obtain ⟨K⟩ := P.exists_spoke_loops ht hY hFY hFports
  have hpoint (i : Fin 5) :
      G.familyCrossingDegree (G.familyTrackComponents {F}) (edgeComponent (Q.dart i))≤
        l38BinCapacity (K.faceSector H) (l38BankBin i) := by
    have hface : G.sourceFace (Q.dart i)=H := Q.face i
    obtain ⟨hmax,hs,hd⟩ := K.source_crossing_data ht hY hFY hFports (Q.dart i)
      (by rw [hface]; exact hY.subset_defects hHY) (by rw [hface]; exact hne)
    apply l38_degree_le_bin_capacity _ _ _ hmax
    · intro hp
      have hh := hs hp
      change P.SingleSectorCone (Q.normal i) (K.faceSector (G.sourceFace (Q.dart i))) at hh
      rw [hface,← E.phase i] at hh
      exact D.single_bin P _ _ _ (E.bounds i) hh
    · intro hp
      have hh := hd hp
      change P.DoubleSectorCone (Q.normal i) (K.faceSector (G.sourceFace (Q.dart i))) at hh
      rw [hface,← E.phase i] at hh
      exact D.double_bin P _ _ _ (E.bounds i) hh
  have htracks : G.familyTrackComponents {H}=
      Finset.univ.image (fun i : Fin 5 => edgeComponent (Q.dart i)) := by
    rw [PennyGraph.familyTrackComponents,G.familySourcePorts_singleton,← Q.darts,Finset.image_image]
    rfl
  have hinj := Q.boundary_spoke_component_injective ht hY hHY hHports
  rw [G.interFamilyCrossings_eq_degree_sum ht {F} {H},htracks,
    Finset.sum_image (fun i _ j _ h => hinj h)]
  exact (Finset.sum_le_sum (fun i _ => hpoint i)).trans
    (l38_bin_capacity_sum_le_three (K.faceSector H))

theorem PennyGraph.isolated_pentagon_pair_crossings_le_three
    {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    {F H : PlaneFace G} (P : PentagonFaceBoundary G F) (Q : PentagonFaceBoundary G H)
    (hFY : F∈Y) (hHY : H∈Y) (hne : H≠F)
    (hFports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (hHports : ∀ s∈G.faceSourcePorts H,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (ρ : ℝ) (i j k l : Fin 5) (hij : i≠j) (hkl : k≠l)
    (hi : Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (P.normal i))
    (hj : Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (P.normal j))
    (hk : Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (Q.normal k))
    (hl : Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+1/2)) (Q.normal l)) :
    G.interFamilyCrossings ht {F} {H}≤3 := by
  obtain ⟨P',⟨D⟩⟩ := P.exists_bank_bin_boundary_of_sharp_pair ht (hY.subset_defects hFY) ρ i j hij hi hj
  obtain ⟨Q',⟨E⟩⟩ := Q.exists_bank_bin_boundary_of_sharp_pair ht (hY.subset_defects hHY) ρ k l hkl hk hl
  exact G.isolated_pentagon_pair_crossings_le_three_of_bins ht hY P' Q' hFY hHY hne hFports hHports D E

end Swanepoel
