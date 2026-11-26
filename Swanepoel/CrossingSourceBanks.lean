module
public import Swanepoel.OrdinaryCutBanks
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem SpineTransition.reverse_reverse {n : ℕ} {G : PennyGraph n} (q : SpineTransition G) :
    q.reverse.reverse=q := by
  apply Subtype.ext
  simp only [SpineTransition.reverse,reverseEdge_involutive]

theorem crossing_cut_transition_before_source {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (cut : TrackComponent G) (e : OrientedEdge G)
    (he : SpineSource e) (hne : edgeComponent e≠cut)
    (hcross : ComponentCrosses (edgeComponent e) cut) :
    ∃ q : SpineTransition G, cutRhombus cut q.rhombus ∧
      Relation.ReflTransGen PositiveCellStep e q.val.1 ∧
      ∀ p : SpineTransition G,
        (edgeComponent p.val.1=edgeComponent q.val.1 ∧ cutRhombus cut p.rhombus) ↔
          p=q ∨ p=q.reverse := by
  obtain ⟨q,hqc,hqcut,hpairs⟩ := crossing_cut_transition_pair ht (edgeComponent e) cut hne hcross
  obtain ⟨s,t,hs,htop,hE,hall⟩ := component_spine_iff ht e
  have hse : s=e := source_path_eq he hE.1
  subst s
  rcases (hall q.val.1).mp hqc with hq | hq
  · refine ⟨q,hqcut,hq.1,?_⟩
    intro p
    simpa only [hqc] using hpairs p
  · have hr := (onSpine_reverse_iff.mp hq).1
    have hprefix : Relation.ReflTransGen PositiveCellStep e q.reverse.val.1 :=
      spine_prefix_closed ht hs hr q.property.reverse
    refine ⟨q.reverse,?_,hprefix,?_⟩
    · rwa [q.reverse_rhombus]
    · intro p
      have hc := q.reverse_component.trans hqc
      simpa only [hc,q.reverse_reverse,or_comm] using hpairs p

theorem path_before_global_cut_preserved {n : ℕ} {G : PennyGraph n}
    (cut : TrackComponent G) (q : SpineTransition G)
    (hpairs : ∀ p : SpineTransition G,
      (edgeComponent p.val.1=edgeComponent q.val.1 ∧ cutRhombus cut p.rhombus) ↔
        p=q ∨ p=q.reverse)
    {e : OrientedEdge G} (hpath : Relation.ReflTransGen PositiveCellStep e q.val.1) :
    Relation.ReflTransGen (TrackCutStep cut) e q.val.1 := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hab hbe ih =>
    apply ih.head
    let p : SpineTransition G := ⟨(a,b),hab⟩
    refine ⟨p,rfl,?_⟩
    intro hpcut
    have hcomp : edgeComponent p.val.1=edgeComponent q.val.1 :=
      positive_path_component (hbe.head hab)
    rcases (hpairs p).mp ⟨hcomp,hpcut⟩ with hp | hp
    · have hb : b=q.val.2 := congrArg (fun p : SpineTransition G => p.val.2) hp
      have hbe' : Relation.ReflTransGen PositiveCellStep q.val.2 q.val.1 := by simpa only [hb] using hbe
      exact no_closed_positive_spine q.val.1 (Relation.TransGen.head' q.property hbe')
    · have hb : b=reverseEdge q.val.1 := congrArg (fun p : SpineTransition G => p.val.2) hp
      exact spine_opposite_sources_ne hbe hb

theorem SpineTransition.other_component_eq_cut {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (cut : TrackComponent G) (q : SpineTransition G)
    (hcut : cutRhombus cut q.rhombus) (hne : edgeComponent q.val.1≠cut)
    (C : RhombusCell G) (hE : q.val.1.val=(C.a,C.b)) (hF : q.val.2.val=(C.d,C.c)) :
    edgeComponent C.edgeAD=cut := by
  have heq : q.val.1=C.edgeAB := Subtype.ext hE
  have hfq : q.val.2=C.edgeDC := Subtype.ext hF
  have hcorners : q.rhombus.representative.corners=C.corners := by
    rw [q.rhombus.representative_corners]
    change stepCorners q.val.1 q.val.2=C.corners
    rw [heq,hfq,C.stepCorners_eq]
  have hp := q.rhombus.representative.trackPair_of_corners ht C hcorners
  change s(edgeComponent q.rhombus.representative.edgeAB,
    edgeComponent q.rhombus.representative.edgeAD)=s(edgeComponent C.edgeAB,edgeComponent C.edgeAD) at hp
  have hCAB : edgeComponent C.edgeAB≠cut := by simpa only [heq] using hne
  rcases Sym2.eq_iff.mp hp with h | h
  · rcases hcut with hh | hh
    · exact False.elim (hCAB (h.1.symm.trans hh))
    · exact h.2.symm.trans hh
  · rcases hcut with hh | hh
    · exact h.1.symm.trans hh
    · exact False.elim (hCAB (h.2.symm.trans hh))

theorem OrdinaryCutBanks.crossing_source_label {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)
    (e : OrientedEdge G) (he : SpineSource e)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht)
    (hcross : ComponentCrosses (edgeComponent e) cut) :
    (0 < inner ℝ B.vector (sourceNormal e) ∧ B.faceLabel (G.sourceFace e)=B.positiveLabel) ∨
      (inner ℝ B.vector (sourceNormal e)<0 ∧ B.faceLabel (G.sourceFace e)=B.negativeLabel) := by
  have hne : edgeComponent e≠cut := (componentGraph G ht).ne_of_adj hcross
  obtain ⟨q,hqcut,hprefix,hpairs⟩ := crossing_cut_transition_before_source ht cut e he hne hcross
  have hpath := path_before_global_cut_preserved cut q hpairs hprefix
  have hlabels := trackCut_path_start_vertex_winding_eq ht cut B.outer B.loop B.support hpath
  obtain ⟨C,hE,hF,hpos⟩ := q.property
  have hqne : edgeComponent q.val.1≠cut := by
    rwa [← positive_path_component hprefix]
  have hAD := q.other_component_eq_cut ht cut hqcut hqne C hE hF
  have hvector : carriedVector e=C.u := by
    rw [positive_path_vector_eq hprefix]
    simp only [carriedVector,hE,RhombusCell.u]
  have hdot : inner ℝ B.vector (sourceNormal e)=cross2 B.vector C.u := by
    rw [sourceNormal_inner_eq_cross,hvector]
  have hswap : cross2 C.v C.u= -cross2 C.u C.v := by unfold cross2; ring
  have hflabel : B.faceLabel (G.sourceFace e)=B.vertexLabel C.a := by
    rw [← B.defect_source_vertex_label ht e heF]
    simpa only [hE,OrdinaryCutBanks.vertexLabel] using hlabels
  rcases B.vector_sameLine C.edgeAD hAD with hv | hv
  · change C.v=B.vector at hv
    right
    refine ⟨?_,?_⟩
    · rw [hdot,← hv,hswap]
      linarith
    · rw [hflabel]
      exact B.cut_edge_start_label_of_eq ht hAD hv
  · change C.v= -B.vector at hv
    have hneg : B.vector= -C.v := by rw [hv,neg_neg]
    left
    refine ⟨?_,?_⟩
    · rw [hdot,hneg,cross2_neg_left,hswap]
      linarith
    · rw [hflabel]
      exact B.cut_edge_start_label_of_neg ht hAD hv

end Swanepoel
