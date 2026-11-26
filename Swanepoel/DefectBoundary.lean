module
public import Swanepoel.DefectPortRealization
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem cross2_neg_left (u z : Plane) : cross2 (-u) z = -cross2 u z := by
  simp [cross2]
  ring

theorem leftHalfBall_neg (u p : Plane) (r : ℝ) :
    leftHalfBall (-u) p r = rightHalfBall u p r := by
  ext z
  simp only [leftHalfBall, rightHalfBall, Set.mem_inter_iff, Set.mem_ofPred_eq,
    cross2_neg_left, neg_lt_neg_iff]

theorem PennyGraph.right_halfBall_subset_sourceFace {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) :
    rightHalfBall (carriedVector e) (G.edgePoint e.val.1 e.val.2 (1/2))
      (2*G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2)) ⊆
        (G.sourceFace e).val := by
  have he : physicalEdge e ∉ G.sourceProbeDrawing e := by simp [PennyGraph.sourceProbeDrawing]
  have hdrawing : G.subdrawing (insert (physicalEdge e) (G.sourceProbeDrawing e)) = G.drawing := by
    simp only [PennyGraph.sourceProbeDrawing,
      Finset.insert_erase (Finset.mem_univ _), G.subdrawing_univ]
  have hsides := G.edge_sides_in_fixed_components (G.sourceProbeDrawing e) (physicalEdge e) he
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  rw [hdrawing, physicalEdge_midpoint] at hsides
  have hchoose :
      (if sourceProbeSide e then
        leftHalfBall (G.point (physicalEdge e).val.2-G.point (physicalEdge e).val.1)
          (G.edgePoint e.val.1 e.val.2 (1/2))
          (2*G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2))
      else
        rightHalfBall (G.point (physicalEdge e).val.2-G.point (physicalEdge e).val.1)
          (G.edgePoint e.val.1 e.val.2 (1/2))
          (2*G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2))) ⊆
        (G.sourceFace e).val := by
    cases hb : sourceProbeSide e
    · simpa only [hb, Bool.false_eq_true, ↓reduceIte, PennyGraph.sourceFace,
        PennyGraph.sourceProbe] using hsides.2
    · simpa only [hb, ↓reduceIte, PennyGraph.sourceFace, PennyGraph.sourceProbe] using hsides.1
  by_cases h : e.val.1 < e.val.2
  · have h' : ¬ e.val.2 < e.val.1 := not_lt_of_ge h.le
    simpa only [sourceProbeSide, h', decide_false, Bool.false_eq_true, ↓reduceIte,
      physicalEdge, dite_eq_left h, carriedVector] using hchoose
  · have h' : e.val.2 < e.val.1 := lt_of_le_of_ne (le_of_not_gt h) e.property.ne.symm
    have hv : G.point e.val.1-G.point e.val.2 = -carriedVector e := by
      dsimp [carriedVector]
      abel
    simpa only [sourceProbeSide, h', decide_true, ↓reduceIte,
      physicalEdge, dite_eq_right h, hv, leftHalfBall_neg] using hchoose

theorem PennyGraph.sourceFace_eq_rhombus_of_negative_ab {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (e : OrientedEdge G) (C : RhombusCell G)
    (hab : e.val = (C.a,C.b)) (hneg : cross2 C.u C.v < 0) :
    (G.sourceFace e).val = C.openRegion := by
  let δ := G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2)
  let s := min δ (1/2)
  have hδ : 0 < δ := G.sourceProbe_offset_pos e
  have hs0 : 0 < s := lt_min hδ (by norm_num)
  have hsδ : s ≤ δ := min_le_left _ _
  have hs1 : s < 1 := (min_le_right δ (1/2)).trans_lt (by norm_num)
  let z := C.cellPoint (1/2) s
  have hzin : z ∈ C.openRegion :=
    C.cellPoint_mem_openRegion ht (by norm_num) (by norm_num) hs0 hs1
  have hu : carriedVector e = C.u := by simp only [carriedVector, hab, RhombusCell.u]
  have hmid : G.edgePoint e.val.1 e.val.2 (1/2) = C.cellPoint (1/2) 0 := by
    simpa only [hab] using C.edgePoint_ab (1/2)
  have hzmid : z-G.edgePoint e.val.1 e.val.2 (1/2) = s • C.v := by
    rw [hmid]
    dsimp [z, RhombusCell.cellPoint]
    module
  have hvnorm : ‖C.v‖ = 1 := by
    simpa only [RhombusCell.v, ← dist_eq_norm] using C.da.2
  have hzball : z ∈ Metric.ball (G.edgePoint e.val.1 e.val.2 (1/2)) (2*δ) := by
    rw [Metric.mem_ball, dist_eq_norm, hzmid, norm_smul, hvnorm,
      Real.norm_eq_abs, abs_of_pos hs0, mul_one]
    linarith
  have hzcross : cross2 (carriedVector e) z <
      cross2 (carriedVector e) (G.edgePoint e.val.1 e.val.2 (1/2)) := by
    have hc : cross2 C.u (z-G.edgePoint e.val.1 e.val.2 (1/2)) < 0 := by
      rw [hzmid, cross2_smul_right]
      exact mul_neg_of_pos_of_neg hs0 hneg
    rw [cross2_sub_right] at hc
    rw [hu]
    linarith
  have hzface : z ∈ (G.sourceFace e).val :=
    G.right_halfBall_subset_sourceFace e ⟨hzball, hzcross⟩
  exact ((G.sourceFace e).property.eq_component hzface).trans
    ((C.isBoundedFace ht).1.eq_component hzin).symm

theorem RhombusCell.port_backwards_corners {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    C.backwards.corners = C.corners := by
  ext i
  simp only [RhombusCell.backwards, RhombusCell.corners, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem PennyGraph.sourceFace_eq_positive_predecessor_cell {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (e : OrientedEdge G) (C : RhombusCell G)
    (he : e.val = (C.d,C.c)) (hpos : 0 < cross2 C.u C.v) :
    (G.sourceFace e).val = C.openRegion := by
  have hu : C.backwards.u = C.u := C.opposite_vectors.symm
  have hv : C.backwards.v = -C.v := by
    change G.point C.a-G.point C.d = -(G.point C.d-G.point C.a)
    abel
  have hneg : cross2 C.backwards.u C.backwards.v < 0 := by
    rw [hu, hv]
    have hc : cross2 C.u (-C.v) = -cross2 C.u C.v := by simp [cross2]; ring
    rw [hc]
    linarith
  exact (G.sourceFace_eq_rhombus_of_negative_ab ht e C.backwards he hneg).trans
    (C.backwards.openRegion_eq_of_corners ht C C.port_backwards_corners)

theorem PositiveCellStep.target_sourceFace_eq {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {f e : OrientedEdge G} (h : PositiveCellStep f e) :
    ∃ C : RhombusCell G, (G.sourceFace e).val = C.openRegion := by
  obtain ⟨C, _, he, hpos⟩ := h
  exact ⟨C, G.sourceFace_eq_positive_predecessor_cell ht e C he hpos⟩

theorem PennyGraph.sourceFace_rhombic_iff_not_source {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (e : OrientedEdge G) :
    (∃ C : RhombusCell G, (G.sourceFace e).val = C.openRegion) ↔ ¬ SpineSource e := by
  constructor
  · rintro ⟨C, hC⟩ he
    exact G.sourceFace_ne_rhombus ht e he C hC
  · intro he
    have hp : ∃ f, PositiveCellStep f e := not_not.mp he
    obtain ⟨f, hf⟩ := hp
    exact hf.target_sourceFace_eq ht

theorem PennyGraph.spineSource_of_sourceFace_mem_defects {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (e : OrientedEdge G)
    (hdef : G.sourceFace e ∈ G.defectPlaneFaces ht) : SpineSource e := by
  by_contra he
  obtain ⟨C, hC⟩ := (G.sourceFace_rhombic_iff_not_source ht e).mpr he
  obtain ⟨F, hF, hface⟩ := Finset.mem_image.mp hdef
  have hnot := (Finset.mem_sdiff.mp hF).2
  apply hnot
  let R : RhombusSet G := ⟨C.corners, ⟨C, rfl⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨R, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  have hcorner : R.representative.corners = C.corners := R.representative_corners
  have hrep := R.representative.openRegion_eq_of_corners ht C hcorner
  exact hrep.trans (hC.symm.trans (congrArg (fun H : PlaneFace G => H.val) hface).symm)

theorem PennyGraph.defect_faceSourcePorts_eq_incident {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) :
    G.faceSourcePorts F = Finset.univ.filter (fun e : OrientedEdge G => G.sourceFace e = F) := by
  ext e
  simp only [PennyGraph.faceSourcePorts, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro he
    have hdef : G.sourceFace e ∈ G.defectPlaneFaces ht := by rwa [he]
    exact ⟨G.spineSource_of_sourceFace_mem_defects ht e hdef, he⟩

end Swanepoel
