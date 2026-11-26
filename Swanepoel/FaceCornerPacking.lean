module
public import Swanepoel.FullCornerSectors
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Real
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PennyGraph.faceCornerRegion {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (v : Fin n) : Set Plane :=
  F.val ∩ Metric.ball (G.point v) (1/2:ℝ)

theorem PennyGraph.faceCornerRegion_measurable {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (v : Fin n) : MeasurableSet (G.faceCornerRegion F v) :=
  (F.property.isOpen.inter Metric.isOpen_ball).measurableSet

theorem PennyGraph.faceCornerRegion_finite {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (v : Fin n) : volume (G.faceCornerRegion F v)≠⊤ :=
  (Metric.isBounded_ball.subset Set.inter_subset_right).measure_lt_top.ne

theorem PennyGraph.faceCornerRegions_pairwiseDisjoint {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) : Pairwise (fun v w => Disjoint (G.faceCornerRegion F v) (G.faceCornerRegion F w)) := by
  intro v w hvw
  apply Set.disjoint_left.mpr
  intro z hzv hzw
  have hv : dist z (G.point v)<1/2 := hzv.2
  have hw : dist z (G.point w)<1/2 := hzw.2
  have hsep := G.separated v w hvw
  have htri := dist_triangle (G.point v) z (G.point w)
  rw [dist_comm (G.point v) z] at htri
  linarith

theorem PennyGraph.face_corner_measure_sum_le {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (S : Finset (Fin n)) :
    (∑ v∈S,volume (G.faceCornerRegion F v))≤volume F.val := by
  rw [← measure_biUnion_finset (μ := volume)
    ((G.faceCornerRegions_pairwiseDisjoint F).set_pairwise S)
    (fun v _ => G.faceCornerRegion_measurable F v)]
  apply measure_mono
  intro z hz
  obtain ⟨v,_,hzv⟩ := Set.mem_iUnion₂.mp hz
  exact hzv.1

theorem PennyGraph.face_corner_area_sum_le {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (hF : Bornology.IsBounded F.val) (S : Finset (Fin n)) :
    (∑ v∈S,volume.real (G.faceCornerRegion F v))≤volume.real F.val := by
  rw [← measureReal_biUnion_finset
    ((G.faceCornerRegions_pairwiseDisjoint F).set_pairwise S)
    (fun v _ => G.faceCornerRegion_measurable F v)
    (fun v _ => G.faceCornerRegion_finite F v)]
  apply measureReal_mono _ hF.measure_lt_top.ne
  intro z hz
  obtain ⟨v,_,hzv⟩ := Set.mem_iUnion₂.mp hz
  exact hzv.1

theorem PennyGraph.rotation_half_sector_subset_corner {n : ℕ} (G : PennyGraph n)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (v : Fin n) (a : VertexRay G v) :
    fullClockwiseVertexSector (G.point v) (G.vertexDirection v a)
      (G.vertexDirection v (G.vertexRayRotation v a)) (1/2) ⊆
      G.faceCornerRegion (G.sourceFace ⟨(v,a.val),a.property⟩) v := by
  intro z hz
  exact ⟨G.rotation_half_sector_subset_face hdegree v a hz,
    fullClockwiseVertexSector_subset_ball _ _ _ _ hz⟩

end Swanepoel
