module
public import Swanepoel.RhombusRetainedSignedArea
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace RhombusCell
variable {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)

theorem portRotate_u : C.portRotate.u=C.v := by
  change G.point C.c-G.point C.b=G.point C.d-G.point C.a
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using C.parallelogram)

theorem portRotate_v : C.portRotate.v= -C.u := by
  change G.point C.a-G.point C.b= -(G.point C.b-G.point C.a)
  abel

theorem portRotate_cross : cross2 C.portRotate.u C.portRotate.v=cross2 C.u C.v := by
  rw [C.portRotate_u,C.portRotate_v]
  unfold cross2
  simp
  ring

theorem portReverse_cross : cross2 C.portReverse.u C.portReverse.v= -cross2 C.u C.v := by
  have hu : C.portReverse.u= -C.u := by
    change G.point C.a-G.point C.b= -(G.point C.b-G.point C.a)
    abel
  have hv : C.portReverse.v=C.v := C.portRotate_u
  rw [hu,hv,cross2_neg_left]

theorem sourceFace_ab_iff_negative (ht : G.TriangleFree) :
    (G.sourceFace C.edgeAB).val=C.openRegion ↔ cross2 C.u C.v<0 := by
  constructor
  · intro hface
    have hp := G.sourceProbe_mem_sourceFace C.edgeAB
    rw [hface] at hp
    let δ := G.edgeClearance (G.sourceProbeDrawing C.edgeAB) (physicalEdge C.edgeAB) (1/2)
    have hδ : 0<δ := G.sourceProbe_offset_pos C.edgeAB
    have hoff : G.sourceProbe C.edgeAB-G.point C.a=
        (1/2:ℝ) • C.u+(-δ) • quarterTurn C.u := by
      rw [G.sourceProbe_eq_normal_offset C.edgeAB]
      change G.edgePoint C.a C.b (1/2)+δ • sourceNormal C.edgeAB-G.point C.a=_
      rw [C.edgePoint_ab (1/2)]
      change C.cellPoint (1/2) 0+δ • (-quarterTurn C.u)-G.point C.a=_
      dsimp [cellPoint]
      module
    have hnorm : ‖C.u‖=1 := carriedVector_norm C.edgeAB
    have hcross : cross2 C.u (G.sourceProbe C.edgeAB-G.point C.a)= -δ := by
      rw [hoff,cross2_add_right,cross2_smul_right,cross2_smul_right,
        cross2_self,cross_quarterTurn,hnorm]
      ring
    have hcoord : 0< -δ/cross2 C.u C.v := by
      simpa only [openRegion,Set.mem_ofPred_eq,coordV,hcross] using hp.2.2.1
    rcases div_pos_iff.mp hcoord with ⟨h,_⟩ | ⟨_,h⟩
    · linarith
    · exact h
  · exact G.sourceFace_eq_rhombus_of_negative_ab ht C.edgeAB C rfl

theorem incident_eq_ab_of_unordered (ht : G.TriangleFree) (hneg : cross2 C.u C.v<0)
    (e : OrientedEdge G) (hface : (G.sourceFace e).val=C.openRegion)
    (he : s(e.val.1,e.val.2)=s(C.a,C.b)) : e=C.edgeAB := by
  rcases Sym2.eq_iff.mp he with h | h
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · have heq : e=C.portReverse.edgeAB := Subtype.ext (Prod.ext h.1 h.2)
    have hfaceR : (G.sourceFace C.portReverse.edgeAB).val=C.portReverse.openRegion := by
      rw [← heq,hface]
      exact C.openRegion_eq_of_corners ht C.portReverse C.portReverse_corners.symm
    have hn := (C.portReverse.sourceFace_ab_iff_negative ht).mp hfaceR
    rw [C.portReverse_cross] at hn
    linarith

theorem faceIncidentDarts_of_negative (ht : G.TriangleFree) (hneg : cross2 C.u C.v<0)
    (F : PlaneFace G) (hF : F.val=C.openRegion) :
    G.faceIncidentDarts F={C.edgeAB,C.edgeBC,C.edgeCD,C.edgeDA} := by
  have hfaceD (D : RhombusCell G) (hc : D.corners=C.corners) (hD : cross2 D.u D.v<0) :
      G.sourceFace D.edgeAB=F := by
    apply Subtype.ext
    exact ((D.sourceFace_ab_iff_negative ht).mpr hD).trans
      ((D.openRegion_eq_of_corners ht C hc).trans hF.symm)
  have hR := C.portRotate_cross
  have hRR : cross2 C.portRotate.portRotate.u C.portRotate.portRotate.v=cross2 C.u C.v :=
    C.portRotate.portRotate_cross.trans hR
  have hRRR : cross2 C.portRotate.portRotate.portRotate.u C.portRotate.portRotate.portRotate.v=cross2 C.u C.v :=
    C.portRotate.portRotate.portRotate_cross.trans hRR
  have hcorn2 := C.portRotate.portRotate_corners.trans C.portRotate_corners
  have hcorn3 := C.portRotate.portRotate.portRotate_corners.trans hcorn2
  ext e
  constructor
  · intro he
    have heF : (G.sourceFace e).val=C.openRegion :=
      (congrArg Subtype.val (Finset.mem_filter.mp he).2).trans hF
    obtain ⟨ha,hb⟩ := C.incident_edge_endpoints ht e heF
    have go (D : RhombusCell G) (hc : D.corners=C.corners) (hn : cross2 D.u D.v<0)
        (hab : s(e.val.1,e.val.2)=s(D.a,D.b)) : e=D.edgeAB :=
      D.incident_eq_ab_of_unordered ht hn e
        (heF.trans (C.openRegion_eq_of_corners ht D hc.symm)) hab
    rcases C.adj_inside ht _ _ ha hb e.property with h | h | h | h
    · exact Finset.mem_insert.mpr (Or.inl (go C rfl hneg h))
    · have heq := go C.portRotate C.portRotate_corners (by rwa [hR]) h
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl heq)))
    · have heq := go C.portRotate.portRotate hcorn2 (by rwa [hRR]) h
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl heq)))))
    · have heq := go C.portRotate.portRotate.portRotate hcorn3 (by rwa [hRRR]) h
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr heq))
  · intro he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases he with rfl | rfl | rfl | rfl
    · exact hfaceD C rfl hneg
    · exact hfaceD C.portRotate C.portRotate_corners (by rwa [hR])
    · exact hfaceD C.portRotate.portRotate hcorn2 (by rwa [hRR])
    · exact hfaceD C.portRotate.portRotate.portRotate hcorn3 (by rwa [hRRR])

theorem faceSignedArea_of_negative (ht : G.TriangleFree) (hneg : cross2 C.u C.v<0)
    (F : PlaneFace G) (hF : F.val=C.openRegion) : G.faceSignedArea G.point F= -cross2 C.u C.v := by
  have h1 : C.edgeAB≠C.edgeBC := fun h => C.ab.ne (congrArg (fun e : OrientedEdge G => e.val.1) h)
  have h2 : C.edgeAB≠C.edgeCD := fun h => C.ac (congrArg (fun e : OrientedEdge G => e.val.1) h)
  have h3 : C.edgeAB≠C.edgeDA := fun h => C.da.ne.symm (congrArg (fun e : OrientedEdge G => e.val.1) h)
  have h4 : C.edgeBC≠C.edgeCD := fun h => C.bc.ne (congrArg (fun e : OrientedEdge G => e.val.1) h)
  have h5 : C.edgeBC≠C.edgeDA := fun h => C.bd (congrArg (fun e : OrientedEdge G => e.val.1) h)
  have h6 : C.edgeCD≠C.edgeDA := fun h => C.cd.ne (congrArg (fun e : OrientedEdge G => e.val.1) h)
  unfold PennyGraph.faceSignedArea
  rw [C.faceIncidentDarts_of_negative ht hneg F hF]
  have ha : C.edgeAB∉({C.edgeBC,C.edgeCD,C.edgeDA} : Finset (OrientedEdge G)) := by simp [h1,h2,h3]
  have hb : C.edgeBC∉({C.edgeCD,C.edgeDA} : Finset (OrientedEdge G)) := by simp [h4,h5]
  have hc : C.edgeCD∉({C.edgeDA} : Finset (OrientedEdge G)) := by simpa using h6
  rw [Finset.sum_insert ha,Finset.sum_insert hb,Finset.sum_insert hc,Finset.sum_singleton]
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  change -(cross2 (G.point C.a) (G.point C.b)+(cross2 (G.point C.b) (G.point C.c)+
    (cross2 (G.point C.c) (G.point C.d)+cross2 (G.point C.d) (G.point C.a))))/2= -cross2 C.u C.v
  rw [hc]
  simp [u,v,cross2]
  ring

theorem faceSignedArea_eq_abs_cross (ht : G.TriangleFree)
    (F : PlaneFace G) (hF : F.val=C.openRegion) : G.faceSignedArea G.point F=|cross2 C.u C.v| := by
  by_cases hn : cross2 C.u C.v<0
  · rw [C.faceSignedArea_of_negative ht hn F hF,abs_of_neg hn]
  · have hp : 0<cross2 C.u C.v := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (C.cross_ne_zero ht))
    have hT : cross2 C.transpose.u C.transpose.v= -cross2 C.u C.v := by
      change cross2 C.v C.u= -cross2 C.u C.v
      unfold cross2
      ring
    have hFT : F.val=C.transpose.openRegion :=
      hF.trans (C.openRegion_eq_of_corners ht C.transpose C.transpose_corners.symm)
    rw [C.transpose.faceSignedArea_of_negative ht (by rw [hT]; linarith) F hFT,hT,neg_neg,abs_of_pos hp]

theorem faceSignedArea_lower (ht : G.TriangleFree) (F : PlaneFace G) (hF : F.val=C.openRegion) :
    Real.sqrt 3/2<G.faceSignedArea G.point F := by
  rw [C.faceSignedArea_eq_abs_cross ht F hF]
  exact C.area_lower ht

end RhombusCell
end Swanepoel
