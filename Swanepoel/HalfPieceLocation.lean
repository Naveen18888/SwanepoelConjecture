module
public import Swanepoel.HalfSourceSelection
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem cutPieceBankCode_path (ht : G.TriangleFree) {e f : OrientedEdge G}
    (hpath : Relation.ReflTransGen (TrackCutStep cut) e f) :
    B.cutPieceBankCode ht (trackCutComponent cut e)=
      B.cutPieceBankCode ht (trackCutComponent cut f) := by
  exact congrArg (B.cutPieceBankCode ht) (Quotient.sound
    (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ hpath))

theorem critical_piece_codes_ne (ht : G.TriangleFree)
    {g h : OrientedEdge G} (C : RhombusCell G)
    (hG : g.val=(C.a,C.b)) (hH : h.val=(C.d,C.c)) (hAD : edgeComponent C.edgeAD=cut) :
    B.cutPieceBankCode ht (trackCutComponent cut g)≠
      B.cutPieceBankCode ht (trackCutComponent cut h) := by
  have hr : edgeComponent (reverseEdge C.edgeAD)=cut := (reverse_component _).symm.trans hAD
  change decide (B.vertexLabel g.val.1=B.positiveLabel)≠
    decide (B.vertexLabel h.val.1=B.positiveLabel)
  simp only [hG,hH]
  rcases B.vector_sameLine C.edgeAD hAD with hv | hv
  · have hA := B.cut_edge_start_label_of_eq ht hAD hv
    have hD := B.cut_edge_start_label_of_neg ht hr (by rw [reverseEdge_vector,hv])
    change B.vertexLabel C.a=B.negativeLabel at hA
    change B.vertexLabel C.d=B.positiveLabel at hD
    simp only [hA,hD,Ne.symm B.labels_ne,decide_false,decide_true]
    decide
  · have hA := B.cut_edge_start_label_of_neg ht hAD hv
    have hD := B.cut_edge_start_label_of_eq ht hr (by rw [reverseEdge_vector,hv,neg_neg])
    change B.vertexLabel C.a=B.positiveLabel at hA
    change B.vertexLabel C.d=B.negativeLabel at hD
    simp only [hA,hD,Ne.symm B.labels_ne,decide_false,decide_true]
    decide

theorem same_bank_onSpine_before_cut (ht : G.TriangleFree) (side : Bool)
    {s t a : OrientedEdge G} (hs : SpineSource s) (htop : ¬∃b,PositiveCellStep t b)
    (q : SpineTransition G) (hqcut : cutRhombus cut q.rhombus)
    (hpairs : ∀ p : SpineTransition G,
      (edgeComponent p.val.1=edgeComponent q.val.1 ∧ cutRhombus cut p.rhombus) ↔
        p=q ∨ p=q.reverse)
    (hprefix : Relation.ReflTransGen PositiveCellStep s q.val.1)
    (hsuffix : Relation.ReflTransGen PositiveCellStep q.val.2 t)
    (ha : OnSpine s t a) (hns : edgeComponent s≠cut)
    (hsCode : B.cutPieceBankCode ht (trackCutComponent cut s)=side)
    (haCode : B.cutPieceBankCode ht (trackCutComponent cut a)=side) :
    OnSpine s q.val.1 a := by
  have hlocal : ∀ x y, OnSpine s t x →
      (TrackCutStep cut x y ↔ PositiveSpineCutStep q.val.1 q.val.2 x y) :=
    fun x y hx => trackCutStep_on_spine_iff ht cut q hqcut
      (fun p hp => (hpairs p).mp hp) hprefix hx
  have hmem : a∈spineVertices s t := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
  rw [spine_cut_partition ht hprefix q.property hsuffix] at hmem
  rcases Finset.mem_union.mp hmem with hbefore | hafter
  · exact (Finset.mem_filter.mp hbefore).2
  · have hat := (Finset.mem_filter.mp hafter).2
    have hh : OnSpine s t q.val.2 := ⟨hprefix.tail q.property,hsuffix⟩
    have hpath := local_cut_path_to_trackCut ht hs htop hlocal (path_after_cut_survives q.property hat.1) hh
    have hcodeH : B.cutPieceBankCode ht (trackCutComponent cut q.val.2)=side :=
      (B.cutPieceBankCode_path ht hpath).trans haCode
    have hcodeG : B.cutPieceBankCode ht (trackCutComponent cut q.val.1)=side :=
      (B.cutPieceBankCode_path ht (path_before_global_cut_preserved cut q hpairs hprefix)).symm.trans hsCode
    obtain ⟨C,hG,hH,_⟩ := q.property
    have hne : edgeComponent q.val.1≠cut := by rwa [← positive_path_component hprefix]
    have hAD := q.other_component_eq_cut ht cut hqcut hne C hG hH
    exact False.elim (B.critical_piece_codes_ne ht C hG hH hAD (hcodeG.trans hcodeH.symm))

theorem noncrossing_carried_vertex_label (ht : G.TriangleFree)
    (e f : OrientedEdge G) (he : SpineSource e) (hc : edgeComponent f=edgeComponent e)
    (hne : edgeComponent e≠cut) (hmiss : ¬ComponentCrosses (edgeComponent e) cut) :
    B.vertexLabel f.val.1=B.vertexLabel e.val.1 := by
  obtain ⟨s,t,hs,htop,hE,hall⟩ := component_spine_iff ht e
  have hse : s=e := source_path_eq he hE.1
  subst s
  rcases (hall f).mp hc with hf | hf
  · have hpath := noncrossing_path_preserved ht hne hmiss hf.1
    exact (trackCut_path_start_vertex_winding_eq ht cut B.outer B.loop B.support hpath).symm
  · have hpath := noncrossing_path_preserved ht hne hmiss (onSpine_reverse_iff.mp hf).1
    have hh := trackCut_path_start_vertex_winding_eq ht cut B.outer B.loop B.support hpath
    have hedge := G.noncut_edge_winding_equal ht cut B.outer B.loop B.support f (hc ▸ hne)
    exact hedge.trans (by simpa only [reverseEdge,OrdinaryCutBanks.vertexLabel] using hh.symm)

theorem noncrossing_carried_piece_code (ht : G.TriangleFree) (side : Bool)
    (e f : OrientedEdge G) (he : SpineSource e)
    (heY : G.sourceFace e∈B.bankDefectFamily ht side)
    (hc : edgeComponent f=edgeComponent e) (hne : edgeComponent e≠cut)
    (hmiss : ¬ComponentCrosses (edgeComponent e) cut) :
    B.cutPieceBankCode ht (trackCutComponent cut f)=side := by
  have hv := B.noncrossing_carried_vertex_label ht e f he hc hne hmiss
  have hcode := B.cutPieceBankCode_source ht e (Finset.mem_filter.mp heY).1
  have heCode : B.cutPieceBankCode ht (trackCutComponent cut e)=side :=
    hcode.trans (Finset.mem_filter.mp heY).2
  change decide (B.vertexLabel f.val.1=B.positiveLabel)=side
  rw [hv]
  exact heCode

end OrdinaryCutBanks
end Swanepoel
