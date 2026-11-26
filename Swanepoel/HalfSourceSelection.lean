module
public import Swanepoel.HalfPieceBanks
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem crossing_source_vertex_label (ht : G.TriangleFree)
    (e : OrientedEdge G) (he : SpineSource e)
    (hcross : ComponentCrosses (edgeComponent e) cut) :
    (0 < inner ℝ B.vector (sourceNormal e) ∧ B.vertexLabel e.val.1=B.positiveLabel) ∨
      (inner ℝ B.vector (sourceNormal e)<0 ∧ B.vertexLabel e.val.1=B.negativeLabel) := by
  have hne : edgeComponent e≠cut := (componentGraph G ht).ne_of_adj hcross
  obtain ⟨q,hqcut,hprefix,hpairs⟩ := crossing_cut_transition_before_source ht cut e he hne hcross
  have hpath := path_before_global_cut_preserved cut q hpairs hprefix
  have hlabels := trackCut_path_start_vertex_winding_eq ht cut B.outer B.loop B.support hpath
  obtain ⟨C,hE,hF,hpos⟩ := q.property
  have hqne : edgeComponent q.val.1≠cut := by rwa [← positive_path_component hprefix]
  have hAD := q.other_component_eq_cut ht cut hqcut hqne C hE hF
  have hvector : carriedVector e=C.u := by
    rw [positive_path_vector_eq hprefix]
    simp only [carriedVector,hE,RhombusCell.u]
  have hdot : inner ℝ B.vector (sourceNormal e)=cross2 B.vector C.u := by
    rw [sourceNormal_inner_eq_cross,hvector]
  have hswap : cross2 C.v C.u= -cross2 C.u C.v := by unfold cross2; ring
  have hlabel : B.vertexLabel e.val.1=B.vertexLabel C.a := by
    simpa only [hE,OrdinaryCutBanks.vertexLabel] using hlabels
  rcases B.vector_sameLine C.edgeAD hAD with hv | hv
  · change C.v=B.vector at hv
    right
    refine ⟨?_,?_⟩
    · rw [hdot,← hv,hswap]
      linarith
    · rw [hlabel]
      exact B.cut_edge_start_label_of_eq ht hAD hv
  · change C.v= -B.vector at hv
    have hneg : B.vector= -C.v := by rw [hv,neg_neg]
    left
    refine ⟨?_,?_⟩
    · rw [hdot,hneg,cross2_neg_left,hswap]
      linarith
    · rw [hlabel]
      exact B.cut_edge_start_label_of_neg ht hAD hv

theorem crossing_source_piece_code (ht : G.TriangleFree)
    (e : OrientedEdge G) (he : SpineSource e)
    (hcross : ComponentCrosses (edgeComponent e) cut) :
    B.cutPieceBankCode ht (trackCutComponent cut e)=decide (0 < inner ℝ B.vector (sourceNormal e)) := by
  change decide (B.vertexLabel e.val.1=B.positiveLabel)=_
  rcases B.crossing_source_vertex_label ht e he hcross with ⟨hp,hl⟩ | ⟨hn,hl⟩
  · simp only [hl,hp,decide_true]
  · simp only [hl,Ne.symm B.labels_ne,decide_false,not_lt.mpr hn.le]

theorem exists_nonanchor_exterior_source (ht : G.TriangleFree) (side : Bool)
    (v : TrackComponent G) (hcross : ComponentCrosses v cut)
    (hnot : v∉B.bankAnchorTracks ht side) :
    ∃ e : OrientedEdge G, SpineSource e ∧ edgeComponent e=v ∧
      B.cutPieceBankCode ht (trackCutComponent cut e)=side ∧
      ¬Bornology.IsBounded (G.sourceFace e).val := by
  obtain ⟨s,t,hs,htop,hout,_⟩ := component_spine_iff ht v.out
  have hsv : edgeComponent s=v :=
    (positive_path_component hout.1).trans (Quotient.out_eq v)
  have hst := hout.1.trans hout.2
  have hrt : SpineSource (reverseEdge t) := by
    rintro ⟨a,ha⟩
    have hh := ha.reverse
    simp only [reverseEdge_involutive] at hh
    exact htop ⟨reverseEdge a,hh⟩
  have hrv : edgeComponent (reverseEdge t)=v :=
    (reverse_component t).symm.trans ((positive_path_component hst).symm.trans hsv)
  have hn := source_normals_opposite ht hs hrt (hrv.trans hsv.symm)
    (Ne.symm (spine_opposite_sources_ne hst))
  have hcS : ComponentCrosses (edgeComponent s) cut := hsv ▸ hcross
  have hcR : ComponentCrosses (edgeComponent (reverseEdge t)) cut := hrv ▸ hcross
  have hcodes : B.cutPieceBankCode ht (trackCutComponent cut (reverseEdge t))=
      !(B.cutPieceBankCode ht (trackCutComponent cut s)) := by
    rw [B.crossing_source_piece_code ht s hs hcS,B.crossing_source_piece_code ht _ hrt hcR,
      hn,inner_neg_right]
    rcases B.crossing_source_vertex_label ht s hs hcS with h | h
    · simp [h.1,show ¬(0:ℝ)< -inner ℝ B.vector (sourceNormal s) by linarith [h.1]]
    · simp [show ¬(0:ℝ) < inner ℝ B.vector (sourceNormal s) by linarith [h.1],neg_pos.mpr h.1]
  by_cases hside : B.cutPieceBankCode ht (trackCutComponent cut s)=side
  · exact ⟨s,hs,hsv,hside,B.nonanchor_source_unbounded ht side s hs hside (hsv ▸ hnot)⟩
  · have hrside : B.cutPieceBankCode ht (trackCutComponent cut (reverseEdge t))=side := by
      rw [hcodes]
      cases hc : B.cutPieceBankCode ht (trackCutComponent cut s) <;> cases side <;> simp_all
    exact ⟨reverseEdge t,hrt,hrv,hrside,
      B.nonanchor_source_unbounded ht side _ hrt hrside (hrv ▸ hnot)⟩

end OrdinaryCutBanks
end Swanepoel
