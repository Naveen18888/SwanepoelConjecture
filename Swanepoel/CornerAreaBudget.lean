module
public import Swanepoel.CornerSectorContainment
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.six_port_corner_area_budget {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (F : PlaneFace G) (hports : 6≤(G.faceSourcePorts F).card) :
    Real.sqrt 3/2<∑ e∈G.faceIncidentDarts F,
      Real.pi*(G.actualCornerAngle ht hdegree e).gap/24 := by
  have hsub : G.faceSourcePorts F⊆G.faceIncidentDarts F := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2.2⟩
  have hm : 6≤(G.faceIncidentDarts F).card := hports.trans (Finset.card_le_card hsub)
  have hmR : (6:ℝ)≤(G.faceIncidentDarts F).card := by exact_mod_cast hm
  have hgap := G.face_corner_gap_sum_lower ht hdegree F
  have hsum : (9:ℝ)≤∑ e∈G.faceIncidentDarts F,(G.actualCornerAngle ht hdegree e).gap := by
    linarith only [hmR,hgap]
  have hweighted : 3*Real.pi/8≤
      Real.pi/24*∑ e∈G.faceIncidentDarts F,(G.actualCornerAngle ht hdegree e).gap := by
    have h := mul_le_mul_of_nonneg_left hsum (show 0≤Real.pi/24 by positivity)
    linarith only [h]
  have hroot := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hnonneg := Real.sqrt_nonneg (3:ℝ)
  have hrootlt : Real.sqrt 3<2 := by nlinarith only [hroot,hnonneg]
  have hstrict : Real.sqrt 3/2<3*Real.pi/8 := by linarith only [hrootlt,Real.pi_gt_three]
  have heq : (∑ e∈G.faceIncidentDarts F,Real.pi*(G.actualCornerAngle ht hdegree e).gap/24)=
      Real.pi/24*∑ e∈G.faceIncidentDarts F,(G.actualCornerAngle ht hdegree e).gap := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq]
  exact hstrict.trans_le hweighted

end Swanepoel
