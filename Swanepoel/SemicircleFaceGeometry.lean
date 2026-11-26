module
public import Swanepoel.FacePortIncidence
public import Swanepoel.SemicirclePorts
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

theorem PennyGraph.face_chord_dist_gt_one {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (a b : Fin n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : G.edgePoint a b t ∈ F.val) :
    1 < dist (G.point a) (G.point b) := by
  have hface := G.face_subset_complement F
  have hab : a ≠ b := by
    intro heq
    subst b
    have hsame : G.edgePoint a a t = G.point a := by
      dsimp [PennyGraph.edgePoint]
      module
    rw [hsame] at hz
    exact hface hz (G.point_mem_drawing a)
  apply G.dist_gt_one_of_nonadj a b hab
  intro hedge
  exact hface hz (G.edgeTrace_subset_drawing a b hedge ⟨t, ⟨ht0,ht1⟩, rfl⟩)

theorem PennyGraph.face_chord_parameters_strict {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (a b : Fin n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : G.edgePoint a b t ∈ F.val) : 0 < t ∧ t < 1 := by
  have hface := G.face_subset_complement F
  constructor
  · by_contra hn
    have heq : t = 0 := le_antisymm (le_of_not_gt hn) ht0
    subst t
    have hv : G.point a ∈ F.val := by simpa [PennyGraph.edgePoint] using hz
    exact hface hv (G.point_mem_drawing a)
  · by_contra hn
    have heq : t = 1 := le_antisymm ht1 (le_of_not_gt hn)
    subst t
    have hv : G.point b ∈ F.val := by simpa [PennyGraph.edgePoint] using hz
    exact hface hv (G.point_mem_drawing b)

def capStripInterior (p u v : Plane) (height : ℝ) : Set Plane :=
  {z | ∃ r ∈ Ioo (0 : ℝ) height, ∃ s ∈ Ioo (0 : ℝ) 1,
    z = p+r • u+s • v}

theorem PennyGraph.translated_cap_contact {n : ℕ} (G : PennyGraph n)
    (a b c d : Fin n) (hab : G.graph.Adj a b)
    (hd : G.point d = G.point c+(G.point b-G.point a)) : G.graph.Adj c d := by
  have hdiff : G.point d-G.point c = G.point b-G.point a := by rw [hd]; abel
  have hnorm : ‖G.point b-G.point a‖ = 1 := by
    simpa only [← dist_eq_norm] using hab.symm.2
  have hdist : dist (G.point c) (G.point d) = 1 := by
    rw [dist_comm, dist_eq_norm, hdiff, hnorm]
  refine ⟨?_, hdist⟩
  intro heq
  rw [heq,dist_self] at hdist
  norm_num at hdist

theorem PennyGraph.unit_cap_strip_not_subset_face {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (a b c d : Fin n) (hab : G.graph.Adj a b)
    (u : Plane) (height t : ℝ) (ht0 : 0 < t) (hth : t < height)
    (hc : G.point c = G.point a+t • u)
    (hd : G.point d = G.point c+(G.point b-G.point a)) :
    ¬ capStripInterior (G.point a) u (G.point b-G.point a) height ⊆ F.val := by
  intro hstrip
  have hmid : G.edgePoint c d (1/2) = G.point a+t • u+
      (1/2 : ℝ) • (G.point b-G.point a) := by
    rw [PennyGraph.edgePoint, hd, hc]
    module
  have hz : G.edgePoint c d (1/2) ∈ F.val := hstrip
    ⟨t, ⟨ht0,hth⟩, 1/2, ⟨by norm_num,by norm_num⟩, hmid⟩
  have hgt := G.face_chord_dist_gt_one F c d (by norm_num) (by norm_num) hz
  have heq := (G.translated_cap_contact a b c d hab hd).2
  linarith

theorem PennyGraph.two_layer_cap_strip_not_face {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (a b c d : Fin n) (hab : G.graph.Adj a b)
    (u : Plane) (hc : G.point c = G.point a+u)
    (hd : G.point d = G.point a+u+(G.point b-G.point a)) :
    ¬ capStripInterior (G.point a) u (G.point b-G.point a) 2 ⊆ F.val := by
  apply G.unit_cap_strip_not_subset_face F a b c d hab u 2 1 (by norm_num) (by norm_num)
  · simpa only [one_smul] using hc
  · rwa [hc]

end Swanepoel
