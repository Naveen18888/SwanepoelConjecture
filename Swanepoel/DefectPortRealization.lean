module
public import Swanepoel.DefectPorts
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.edge_midpoint_mem_closure_side_component {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e ∉ S) (left : Bool) :
    G.edgePoint e.val.1 e.val.2 (1/2) ∈ closure
      (connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e left (1/2))) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let p := G.edgePoint e.val.1 e.val.2 (1/2)
  let δ := G.edgeClearance S e (1/2)
  have hδ : 0 < δ := (G.edgeClearance_spec S e he (by norm_num) (by norm_num)).1
  let d := min δ (ε/2)
  have hd : 0 < d := lt_min hδ (by positivity)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdε : 2*d ≤ ε := by have := min_le_right δ (ε/2); dsimp [d]; linarith
  have hu : ‖G.point e.val.2-G.point e.val.1‖ = 1 := by
    simpa only [← dist_eq_norm] using e.property.2.symm.2
  have hnorm := normal_offset_mem_halfBalls _ p hu hd
  have hsides := G.edge_sides_in_fixed_components S e he (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  cases left
  · refine ⟨p+(-d) • quarterTurn (G.point e.val.2-G.point e.val.1), ?_, ?_⟩
    · exact hsides.2 ⟨(Metric.ball_subset_ball (by linarith : 2*d ≤ 2*δ)) hnorm.2.1,
        hnorm.2.2⟩
    · have hdistance : dist p (p+(-d) • quarterTurn (G.point e.val.2-G.point e.val.1)) < 2*d := by
        simpa only [dist_comm] using Metric.mem_ball.mp hnorm.2.1
      exact hdistance.trans_le hdε
  · refine ⟨p+d • quarterTurn (G.point e.val.2-G.point e.val.1), ?_, ?_⟩
    · exact hsides.1 ⟨(Metric.ball_subset_ball (by linarith : 2*d ≤ 2*δ)) hnorm.1.1,
        hnorm.1.2⟩
    · have hdistance : dist p (p+d • quarterTurn (G.point e.val.2-G.point e.val.1)) < 2*d := by
        simpa only [dist_comm] using Metric.mem_ball.mp hnorm.1.1
      exact hdistance.trans_le hdε

theorem physicalEdge_midpoint {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    G.edgePoint (physicalEdge e).val.1 (physicalEdge e).val.2 (1/2) =
      G.edgePoint e.val.1 e.val.2 (1/2) := by
  by_cases h : e.val.1 < e.val.2
  · simp [physicalEdge, h]
  · simp only [physicalEdge, dite_eq_right h]
    simpa only [show (1 : ℝ)-1/2=1/2 by norm_num] using
      G.edgePoint_reverse e.val.1 e.val.2 (1/2)

theorem PennyGraph.edge_midpoint_mem_closure_sourceFace {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : G.edgePoint e.val.1 e.val.2 (1/2) ∈ closure (G.sourceFace e).val := by
  have h := G.edge_midpoint_mem_closure_side_component (G.sourceProbeDrawing e)
    (physicalEdge e) (by simp [PennyGraph.sourceProbeDrawing]) (sourceProbeSide e)
  simpa only [physicalEdge_midpoint, PennyGraph.sourceProbeDrawing,
    Finset.insert_erase (Finset.mem_univ _), G.subdrawing_univ,
    PennyGraph.sourceFace, PennyGraph.sourceProbe] using h

theorem PennyGraph.sourceProbe_mem_sourceFace {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) : G.sourceProbe e ∈ (G.sourceFace e).val :=
  mem_connectedComponentIn (G.sourceProbe_mem_complement e)

theorem PennyGraph.sourceFace_ne_rhombus_ab {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) (he : SpineSource e)
    (C : RhombusCell G) (hab : e.val = (C.a,C.b)) :
    (G.sourceFace e).val ≠ C.openRegion := by
  intro hface
  have hp := G.sourceProbe_mem_sourceFace e
  rw [hface] at hp
  have hu : carriedVector e = C.u := by simp only [carriedVector, hab, RhombusCell.u]
  let δ := G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2)
  have hδ : 0 < δ := G.sourceProbe_offset_pos e
  have hmid : G.edgePoint e.val.1 e.val.2 (1/2) = C.cellPoint (1/2) 0 := by
    simpa only [hab] using C.edgePoint_ab (1/2)
  have hoff : G.sourceProbe e-G.point C.a =
      (1/2 : ℝ) • C.u + (-δ) • quarterTurn C.u := by
    rw [G.sourceProbe_eq_normal_offset e, hmid]
    simp only [sourceNormal, hu]
    dsimp [RhombusCell.cellPoint, δ]
    module
  have hnorm : ‖C.u‖ = 1 := hu ▸ carriedVector_norm e
  have hcross : cross2 C.u (G.sourceProbe e-G.point C.a) = -δ := by
    rw [hoff, cross2_add_right, cross2_smul_right, cross2_smul_right,
      cross2_self, cross_quarterTurn, hnorm]
    ring
  have hcoord : 0 < -δ/cross2 C.u C.v := by
    simpa only [RhombusCell.openRegion, Set.mem_ofPred_eq, RhombusCell.coordV, hcross] using hp.2.2.1
  have hnegative : cross2 C.u C.v < 0 := by
    rcases div_pos_iff.mp hcoord with ⟨h, _⟩ | ⟨_, h⟩
    · linarith
    · exact h
  have hbacku : C.backwards.u = C.u := C.opposite_vectors.symm
  have hbackv : C.backwards.v = -C.v := by
    change G.point C.a-G.point C.d = -(G.point C.d-G.point C.a)
    abel
  apply he
  refine ⟨⟨(C.d,C.c), C.cd.symm⟩, C.backwards, rfl, ?_, ?_⟩
  · simpa only [RhombusCell.backwards] using hab
  · rw [hbacku, hbackv]
    have hcrossneg : cross2 C.u (-C.v) = -cross2 C.u C.v := by simp [cross2]; ring
    rw [hcrossneg]
    linarith

def RhombusCell.portRotate {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : RhombusCell G where
  a := C.b
  b := C.c
  c := C.d
  d := C.a
  ac := C.bd
  bd := C.ac.symm
  ab := C.bc
  bc := C.cd
  cd := C.da
  da := C.ab

def RhombusCell.portReverse {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : RhombusCell G where
  a := C.b
  b := C.a
  c := C.d
  d := C.c
  ac := C.bd
  bd := C.ac
  ab := C.ab.symm
  bc := C.da.symm
  cd := C.cd.symm
  da := C.bc.symm

theorem RhombusCell.portRotate_corners {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    C.portRotate.corners = C.corners := by
  ext i
  simp only [RhombusCell.portRotate, RhombusCell.corners, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem RhombusCell.portReverse_corners {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    C.portReverse.corners = C.corners := by
  ext i
  simp only [RhombusCell.portReverse, RhombusCell.corners, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem RhombusCell.align_edge_of_midpoint_mem_boundary {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (e : OrientedEdge G)
    (hm : G.edgePoint e.val.1 e.val.2 (1/2) ∈ C.boundary) :
    ∃ D : RhombusCell G, D.corners = C.corners ∧ e.val = (D.a,D.b) := by
  have align (D : RhombusCell G) (hD : D.corners = C.corners)
      (h : s(e.val.1,e.val.2) = s(D.a,D.b)) :
      ∃ D : RhombusCell G, D.corners = C.corners ∧ e.val = (D.a,D.b) := by
    rcases Sym2.eq_iff.mp h with h | h
    · exact ⟨D, hD, Prod.ext h.1 h.2⟩
    · exact ⟨D.portReverse, D.portReverse_corners.trans hD, Prod.ext h.1 h.2⟩
  rcases hm with ((hm | hm) | hm) | hm
  all_goals obtain ⟨t, ⟨ht0,ht1⟩, he⟩ := hm
  · exact align C rfl (G.interior_edge_intersection _ _ _ _ e.property C.ab
      (by norm_num) (by norm_num) ht0 ht1 he.symm)
  · exact align C.portRotate C.portRotate_corners
      (G.interior_edge_intersection _ _ _ _ e.property C.bc
        (by norm_num) (by norm_num) ht0 ht1 he.symm)
  · exact align C.portRotate.portRotate
      (C.portRotate.portRotate_corners.trans C.portRotate_corners)
      (G.interior_edge_intersection _ _ _ _ e.property C.cd
        (by norm_num) (by norm_num) ht0 ht1 he.symm)
  · exact align C.portRotate.portRotate.portRotate
      (C.portRotate.portRotate.portRotate_corners.trans
        (C.portRotate.portRotate_corners.trans C.portRotate_corners))
      (G.interior_edge_intersection _ _ _ _ e.property C.da
        (by norm_num) (by norm_num) ht0 ht1 he.symm)

theorem PennyGraph.sourceFace_ne_rhombus {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (e : OrientedEdge G) (he : SpineSource e)
    (C : RhombusCell G) : (G.sourceFace e).val ≠ C.openRegion := by
  intro hface
  have hcl := G.edge_midpoint_mem_closure_sourceFace e
  rw [hface] at hcl
  have hno : G.edgePoint e.val.1 e.val.2 (1/2) ∉ C.openRegion := by
    intro hp
    apply C.openRegion_subset_complement ht hp
    exact G.edgeTrace_subset_drawing _ _ e.property
      ⟨1/2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hb := (C.closedRegion_subset_open_union_boundary ht (C.closure_openRegion_subset hcl)).resolve_left hno
  obtain ⟨D, hc, hab⟩ := C.align_edge_of_midpoint_mem_boundary e hb
  exact G.sourceFace_ne_rhombus_ab e he D hab
    (hface.trans (C.openRegion_eq_of_corners ht D hc.symm))

theorem PennyGraph.sourceFace_defect_or_unbounded {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (e : OrientedEdge G) (he : SpineSource e) :
    G.sourceFace e ∈ G.defectPlaneFaces ht ∨
      ¬ Bornology.IsBounded (G.sourceFace e).val := by
  by_cases hb : Bornology.IsBounded (G.sourceFace e).val
  · left
    let F : BoundedFace G := ⟨(G.sourceFace e).val, (G.sourceFace e).property, hb⟩
    have hdef : F ∈ G.defectFaces ht := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hr
      obtain ⟨R, _, hR⟩ := Finset.mem_image.mp hr
      exact G.sourceFace_ne_rhombus ht e he R.representative
        (congrArg (fun H : BoundedFace G => H.val) hR).symm
    exact Finset.mem_image.mpr ⟨F, hdef, rfl⟩
  · exact Or.inr hb

end Swanepoel
