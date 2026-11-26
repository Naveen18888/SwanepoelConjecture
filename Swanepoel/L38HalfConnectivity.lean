module
public import Swanepoel.L38HalfExterior
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def cutEndpoint (side : Bool) (e : OrientedEdge G) : Fin n :=
  if B.vertexBankCode e.val.1=side then e.val.1 else e.val.2

theorem cutEndpoint_mem (ht : G.TriangleFree) (side : Bool) (e : OrientedEdge G)
    (he : edgeComponent e=cut) : B.cutEndpoint side e∈B.bankVertices side := by
  have hne := B.cut_vertexBankCode_ne ht e he
  unfold cutEndpoint
  split_ifs with ha
  · exact (B.mem_bankVertices side _).mpr ha
  · apply (B.mem_bankVertices side _).mpr
    cases ha' : B.vertexBankCode e.val.1 <;> cases hb' : B.vertexBankCode e.val.2 <;>
      cases side <;> simp_all

theorem cutEndpoint_reverse (ht : G.TriangleFree) (side : Bool) (e : OrientedEdge G)
    (he : edgeComponent e=cut) : B.cutEndpoint side (reverseEdge e)=B.cutEndpoint side e := by
  have hne := B.cut_vertexBankCode_ne ht e he
  unfold cutEndpoint
  change (if B.vertexBankCode e.val.2=side then e.val.2 else e.val.1)=_
  cases ha : B.vertexBankCode e.val.1 <;> cases hb : B.vertexBankCode e.val.2 <;>
    cases side <;> simp_all

def cutEndpointIndex (ht : G.TriangleFree) (side : Bool) (e : OrientedEdge G)
    (he : edgeComponent e=cut) : Fin (B.bankVertices side).card :=
  B.halfVertexIndex side (B.cutEndpoint side e) (B.cutEndpoint_mem ht side e he)

theorem cutEndpointIndex_reverse (ht : G.TriangleFree) (side : Bool) (e : OrientedEdge G)
    (he : edgeComponent e=cut) :
    B.cutEndpointIndex ht side (reverseEdge e) ((reverse_component e).symm.trans he)=
      B.cutEndpointIndex ht side e he := by
  apply B.halfVertex_injective side
  simp only [cutEndpointIndex,B.halfVertex_index,B.cutEndpoint_reverse ht side e he]

theorem cut_rail_adj (ht : G.TriangleFree) (side : Bool) (e f : OrientedEdge G)
    (he : edgeComponent e=cut) (hf : edgeComponent f=cut) (hef : PositiveCellStep e f) :
    (B.halfGraph side).graph.Adj (B.cutEndpointIndex ht side e he) (B.cutEndpointIndex ht side f hf) := by
  obtain ⟨C,hE,hF,hpos⟩ := hef
  have hAB : edgeComponent C.edgeAB=cut := (congrArg edgeComponent (Subtype.ext hE)).symm.trans he
  have hAD : edgeComponent C.edgeAD≠cut := by
    intro h
    exact ((componentGraph G ht).ne_of_adj (show ComponentCrosses cut cut from ⟨C,Or.inl ⟨hAB,h⟩⟩)) rfl
  have hsame := B.noncut_vertexBankCode_eq ht C.edgeAD hAD
  apply (B.halfGraph_adj_iff side _ _).mpr
  simp only [cutEndpointIndex,B.halfVertex_index]
  unfold cutEndpoint
  simp only [hE,hF]
  by_cases ha : B.vertexBankCode C.a=side
  · have hd : B.vertexBankCode C.d=side := hsame.symm.trans ha
    simp only [ha,hd,ite_true]
    exact C.da.symm
  · have hd : B.vertexBankCode C.d≠side := fun h => ha (hsame.trans h)
    simp only [ha,hd,ite_false]
    exact C.bc

theorem cut_rail_path (ht : G.TriangleFree) (side : Bool) {e f : OrientedEdge G}
    (he : edgeComponent e=cut) (hf : edgeComponent f=cut)
    (hpath : Relation.ReflTransGen PositiveCellStep e f) :
    (B.halfGraph side).graph.Reachable (B.cutEndpointIndex ht side e he) (B.cutEndpointIndex ht side f hf) := by
  induction hpath with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail a b hpath hab ih =>
    have ha : edgeComponent a=cut := (positive_path_component hpath).symm.trans he
    exact (ih ha).trans (B.cut_rail_adj ht side a b ha hf hab).reachable

theorem cut_rail_reachable (ht : G.TriangleFree) (side : Bool) (e : OrientedEdge G)
    (he : edgeComponent e=cut) :
    (B.halfGraph side).graph.Reachable (B.cutEndpointIndex ht side B.start B.component)
      (B.cutEndpointIndex ht side e he) := by
  obtain ⟨s,t,hs,htop,hreach,hall⟩ := component_spine_iff ht B.start
  have hss : s=B.start := source_path_eq B.source hreach.1
  subst s
  have hec : edgeComponent e=edgeComponent B.start := he.trans B.component.symm
  rcases (hall e).mp hec with hp | hp
  · exact B.cut_rail_path ht side B.component he hp.1
  · have hr : edgeComponent (reverseEdge e)=cut := (reverse_component e).symm.trans he
    have hp' := onSpine_reverse_iff.mp hp
    simpa only [B.cutEndpointIndex_reverse ht side e he] using
      B.cut_rail_path ht side B.component hr hp'.1

theorem halfGraph_connected (ht : G.TriangleFree) (hc : G.graph.Connected) (side : Bool) :
    (B.halfGraph side).graph.Connected := by
  let base := B.cutEndpoint side B.start
  have hbase : base∈B.bankVertices side := B.cutEndpoint_mem ht side B.start B.component
  let baseIndex := B.halfVertexIndex side base hbase
  have hwalk : ∀ {a b : Fin n},G.graph.Walk a b → b=base →
      ∀ ha : a∈B.bankVertices side,(B.halfGraph side).graph.Reachable
        (B.halfVertexIndex side a ha) baseIndex := by
    intro a b p
    induction p with
    | nil =>
      intro hb ha
      cases hb
      exact SimpleGraph.Reachable.refl _
    | @cons a b c hab p ih =>
      intro hc ha
      by_cases hb : b∈B.bankVertices side
      · have hadj : (B.halfGraph side).graph.Adj (B.halfVertexIndex side a ha)
            (B.halfVertexIndex side b hb) := by
          apply (B.halfGraph_adj_iff side _ _).mpr
          simpa only [B.halfVertex_index] using hab
        exact hadj.reachable.trans (ih hc hb)
      · let e : OrientedEdge G := ⟨(a,b),hab⟩
        have he : edgeComponent e=cut := by
          by_contra hn
          have hsame := B.noncut_vertexBankCode_eq ht e hn
          exact hb ((B.mem_bankVertices side b).mpr
            (hsame.symm.trans ((B.mem_bankVertices side a).mp ha)))
        have hep : B.cutEndpoint side e=a := by
          change (if B.vertexBankCode a=side then a else b)=a
          rw [ite_eq_left ((B.mem_bankVertices side a).mp ha)]
        have hei : B.cutEndpointIndex ht side e he=B.halfVertexIndex side a ha := by
          apply B.halfVertex_injective side
          simp only [cutEndpointIndex,B.halfVertex_index,hep]
        have hr := (B.cut_rail_reachable ht side e he).symm
        rw [hei] at hr
        exact hr
  have htoBase (i : Fin (B.bankVertices side).card) :
      (B.halfGraph side).graph.Reachable i baseIndex := by
    obtain ⟨p⟩ := hc.preconnected (B.halfVertex side i) base
    have h := hwalk p rfl (B.halfVertex_mem side i)
    have hi : B.halfVertexIndex side (B.halfVertex side i) (B.halfVertex_mem side i)=i := by
      apply B.halfVertex_injective side
      simp only [B.halfVertex_index]
    rwa [hi] at h
  let : Nonempty (Fin (B.bankVertices side).card) := ⟨baseIndex⟩
  exact { preconnected := fun i j => (htoBase i).trans (htoBase j).symm }

end OrdinaryCutBanks
end Swanepoel
