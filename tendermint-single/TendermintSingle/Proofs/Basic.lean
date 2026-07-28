import TendermintSingle.Defs

namespace tendermint_single_indinv

/-- The parameter assumptions used by the TLAPS development.  Finiteness and
non-negativity of set cardinalities are intrinsic to Lean's `Finset.card`. -/
def model_assumptions (s : State) : Prop :=
  s.N > 3 * s.T ∧
    s.N = 3 * s.T + 1 ∧
      (s.Faulty.card : Int) ≤ s.T ∧
        s.Corr ∩ s.Faulty = ∅ ∧
          s.N = (s.Corr.card : Int) + (s.Faulty.card : Int) ∧
            0 ≤ s.N ∧
              0 ≤ s.T ∧
                0 ≤ s.MaxRound ∧
                  -1 ∉ s.ValidValues ∧ s.ValidValues.Nonempty

/-- The protocol parameters are immutable across every generated transition. -/
def same_parameters (s s' : State) : Prop :=
  s'.Corr = s.Corr ∧
    s'.Faulty = s.Faulty ∧
      s'.N = s.N ∧
        s'.T = s.T ∧
          s'.ValidValues = s.ValidValues ∧
            s'.InvalidValues = s.InvalidValues ∧
              s'.MaxRound = s.MaxRound ∧ s'.Proposer = s.Proposer

def all_replicas (s : State) : Finset Int :=
  s.Corr ∪ s.Faulty

def vote_senders (s : State) (msgs : Finset VoteMsg) : Finset Int :=
  Finset.filter (fun p => ∃ m ∈ msgs, p = m.src) (all_replicas s)

def votes_for (v : Int) (msgs : Finset VoteMsg) : Finset VoteMsg :=
  Finset.filter (fun m => v = m.id) msgs

def pv_set (s : State) (r v : Int) : Finset Int :=
  vote_senders s (votes_for v (Finmap.lookupD r s.msgs_prevote))

def pc_set (s : State) (r v : Int) : Finset Int :=
  vote_senders s (votes_for v (Finmap.lookupD r s.msgs_precommit))

noncomputable def proposal_universe (s : State) : Finset ProposalMsg :=
  Finset.image
    (fun x => ProposalMsg.mk x.2.2.1 x.2.1 x.1 x.2.2.2)
    (Finset.product (s.Corr ∪ s.Faulty)
      (Finset.product (Finset.Icc 0 s.MaxRound)
        (Finset.product
          (s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅)
          (Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅))))

noncomputable def prevote_universe (s : State) : Finset VoteMsg :=
  Finset.image
    (fun x => VoteMsg.mk x.2.2 VoteKind.PREVOTE x.2.1 x.1)
    (Finset.product (s.Corr ∪ s.Faulty)
      (Finset.product (Finset.Icc 0 s.MaxRound)
        (s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅)))

noncomputable def precommit_universe (s : State) : Finset VoteMsg :=
  Finset.image
    (fun x => VoteMsg.mk x.2.2 VoteKind.PRECOMMIT x.2.1 x.1)
    (Finset.product (s.Corr ∪ s.Faulty)
      (Finset.product (Finset.Icc 0 s.MaxRound)
        (s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅)))

def action_labels : Finset String :=
  insert "INIT"
    (insert "INSERT_PROPOSAL"
      (insert "UPON_PROPOSAL_PROPOSE"
        (insert "UPON_PROPOSAL_PROPOSE_AND_PREVOTE"
          (insert "UPON_QUORUM_PREVOTES_ANY"
            (insert "UPON_PROPOSAL_PREVOTE_OR_COMMIT_AND_PREVOTE"
              (insert "UPON_QUORUM_PRECOMMITS_ANY"
                (insert "UPON_PROPOSAL_PRECOMMIT_NO_DECISION"
                  (insert "ON_TIMEOUT_PROPOSE"
                    (insert "ON_QUORUM_NIL_PREVOTES"
                      (insert "ON_ROUND_CATCHUP" ∅))))))))))

structure TypeComponents (s : State) : Prop where
  round_keys : Finmap.keys s.round = s.Corr
  round_values : ∀ p ∈ s.Corr,
    Finmap.lookupD p s.round ∈ Finset.Icc 0 s.MaxRound
  step_keys : Finmap.keys s.step = s.Corr
  step_values : ∀ p ∈ s.Corr,
    Finmap.lookupD p s.step ∈
      insert Step.PROPOSE
        (insert Step.PREVOTE
          (insert Step.PRECOMMIT (insert Step.DECIDED (∅ : Finset Step))))
  decision_keys : Finmap.keys s.decision = s.Corr
  decision_values : ∀ p ∈ s.Corr,
    Finmap.lookupD p s.decision ∈ s.ValidValues ∪ insert (-1) ∅
  locked_value_keys : Finmap.keys s.locked_value = s.Corr
  locked_values : ∀ p ∈ s.Corr,
    Finmap.lookupD p s.locked_value ∈ s.ValidValues ∪ insert (-1) ∅
  locked_round_keys : Finmap.keys s.locked_round = s.Corr
  locked_rounds : ∀ p ∈ s.Corr,
    Finmap.lookupD p s.locked_round ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅
  valid_value_keys : Finmap.keys s.valid_value = s.Corr
  valid_values : ∀ p ∈ s.Corr,
    Finmap.lookupD p s.valid_value ∈ s.ValidValues ∪ insert (-1) ∅
  valid_round_keys : Finmap.keys s.valid_round = s.Corr
  valid_rounds : ∀ p ∈ s.Corr,
    Finmap.lookupD p s.valid_round ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅
  proposal_keys : Finmap.keys s.msgs_propose = Finset.Icc 0 s.MaxRound
  proposals_typed : ∀ r ∈ Finset.Icc 0 s.MaxRound,
    ∀ m ∈ Finmap.lookupD r s.msgs_propose, m ∈ proposal_universe s
  proposals_round : ∀ r ∈ Finmap.keys s.msgs_propose,
    ∀ m ∈ Finmap.lookupD r s.msgs_propose, r = m.round
  prevote_keys : Finmap.keys s.msgs_prevote = Finset.Icc 0 s.MaxRound
  prevotes_typed : ∀ r ∈ Finset.Icc 0 s.MaxRound,
    ∀ m ∈ Finmap.lookupD r s.msgs_prevote, m ∈ prevote_universe s
  prevotes_round : ∀ r ∈ Finmap.keys s.msgs_prevote,
    ∀ m ∈ Finmap.lookupD r s.msgs_prevote, r = m.round
  precommit_keys : Finmap.keys s.msgs_precommit = Finset.Icc 0 s.MaxRound
  precommits_typed : ∀ r ∈ Finset.Icc 0 s.MaxRound,
    ∀ m ∈ Finmap.lookupD r s.msgs_precommit, m ∈ precommit_universe s
  precommits_round : ∀ r ∈ Finmap.keys s.msgs_precommit,
    ∀ m ∈ Finmap.lookupD r s.msgs_precommit, r = m.round
  action_typed : s.last_action ∈ action_labels

lemma ind_type_ok_iff_components (s : State) :
    ind_type_ok s ↔ TypeComponents s := by
  unfold ind_type_ok
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩,
      ⟨h9, h10⟩, ⟨h11, h12⟩, ⟨h13, h14⟩, h15, h16, h17,
      h18, h19, h20, h21, h22, h23, h24⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩,
      ⟨h9, h10⟩, ⟨h11, h12⟩, ⟨h13, h14⟩, h15, h16, h17,
      h18, h19, h20, h21, h22, h23, h24⟩

@[simp] lemma lookupD_insert_self {α β : Type} [DecidableEq α] [Inhabited β]
    (a : α) (b : β) (m : Finmap (fun _ : α => β)) :
    Finmap.lookupD a (Finmap.insert a b m) = b := by
  unfold Finmap.lookupD
  rw [Finmap.lookup_insert]
  simp

@[simp] lemma lookupD_insert_of_ne {α β : Type} [DecidableEq α] [Inhabited β]
    {a k : α} (h : a ≠ k) (b : β) (m : Finmap (fun _ : α => β)) :
    Finmap.lookupD a (Finmap.insert k b m) = Finmap.lookupD a m := by
  unfold Finmap.lookupD
  rw [Finmap.lookup_insert_of_ne]
  exact h

lemma finmap_keys_insert_of_mem {α β : Type} [DecidableEq α]
    {m : Finmap (fun _ : α => β)} {S : Finset α} {k : α} {v : β}
    (hkeys : Finmap.keys m = S) (hk : k ∈ S) :
    Finmap.keys (Finmap.insert k v m) = S := by
  ext x
  rw [Finmap.mem_keys, Finmap.mem_insert, ← Finmap.mem_keys, hkeys]
  constructor
  · rintro (rfl | hx)
    · exact hk
    · exact hx
  · exact fun hx => Or.inr hx

lemma finmap_insert_preserves_values {α β : Type}
    [DecidableEq α] [Inhabited β]
    {m : Finmap (fun _ : α => β)} {S : Finset α}
    {P : α → β → Prop} {k : α} {v : β}
    (hkeys : Finmap.keys m = S)
    (hvalues : ∀ a ∈ S, P a (Finmap.lookupD a m))
    (hk : k ∈ S) (hv : P k v) :
    Finmap.keys (Finmap.insert k v m) = S ∧
      ∀ a ∈ S, P a (Finmap.lookupD a (Finmap.insert k v m)) := by
  constructor
  · exact finmap_keys_insert_of_mem hkeys hk
  · intro a ha
    by_cases hak : a = k
    · subst a
      simpa using hv
    · rw [lookupD_insert_of_ne hak]
      exact hvalues a ha

lemma lookupD_subset_insert_union {α β : Type}
    [DecidableEq α] [DecidableEq β] [Inhabited (Finset β)]
    (query key : α) (added : Finset β)
    (m : Finmap (fun _ : α => Finset β)) :
    Finmap.lookupD query m ⊆
      Finmap.lookupD query
        (Finmap.insert key (Finmap.lookupD key m ∪ added) m) := by
  intro x hx
  by_cases hqk : query = key
  · subst query
    rw [lookupD_insert_self]
    exact Finset.mem_union.mpr (Or.inl hx)
  · rw [lookupD_insert_of_ne hqk]
    exact hx

lemma proposal_mk_mem_universe {s : State} {src r v vr : Int}
    (hsrc : src ∈ s.Corr ∪ s.Faulty)
    (hr : r ∈ Finset.Icc 0 s.MaxRound)
    (hv : v ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅)
    (hvr : vr ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅) :
    ProposalMsg.mk v r src vr ∈ proposal_universe s := by
  unfold proposal_universe
  apply Finset.mem_image.mpr
  refine ⟨(src, r, v, vr), ?_, rfl⟩
  exact Finset.mem_product.mpr
    ⟨hsrc, Finset.mem_product.mpr
      ⟨hr, Finset.mem_product.mpr ⟨hv, hvr⟩⟩⟩

lemma prevote_mk_mem_universe {s : State} {src r v : Int}
    (hsrc : src ∈ s.Corr ∪ s.Faulty)
    (hr : r ∈ Finset.Icc 0 s.MaxRound)
    (hv : v ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅) :
    VoteMsg.mk v VoteKind.PREVOTE r src ∈ prevote_universe s := by
  unfold prevote_universe
  apply Finset.mem_image.mpr
  refine ⟨(src, r, v), ?_, rfl⟩
  exact Finset.mem_product.mpr
    ⟨hsrc, Finset.mem_product.mpr ⟨hr, hv⟩⟩

lemma precommit_mk_mem_universe {s : State} {src r v : Int}
    (hsrc : src ∈ s.Corr ∪ s.Faulty)
    (hr : r ∈ Finset.Icc 0 s.MaxRound)
    (hv : v ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) ∅) :
    VoteMsg.mk v VoteKind.PRECOMMIT r src ∈ precommit_universe s := by
  unfold precommit_universe
  apply Finset.mem_image.mpr
  refine ⟨(src, r, v), ?_, rfl⟩
  exact Finset.mem_product.mpr
    ⟨hsrc, Finset.mem_product.mpr ⟨hr, hv⟩⟩

structure ProposalMapFacts (s : State)
    (msgs : Finmap (fun _ : Int => Finset ProposalMsg)) : Prop where
  keys : Finmap.keys msgs = Finset.Icc 0 s.MaxRound
  typed : ∀ r ∈ Finset.Icc 0 s.MaxRound,
    ∀ m ∈ Finmap.lookupD r msgs, m ∈ proposal_universe s
  round : ∀ r ∈ Finmap.keys msgs,
    ∀ m ∈ Finmap.lookupD r msgs, r = m.round

structure PrevoteMapFacts (s : State)
    (msgs : Finmap (fun _ : Int => Finset VoteMsg)) : Prop where
  keys : Finmap.keys msgs = Finset.Icc 0 s.MaxRound
  typed : ∀ r ∈ Finset.Icc 0 s.MaxRound,
    ∀ m ∈ Finmap.lookupD r msgs, m ∈ prevote_universe s
  round : ∀ r ∈ Finmap.keys msgs,
    ∀ m ∈ Finmap.lookupD r msgs, r = m.round

structure PrecommitMapFacts (s : State)
    (msgs : Finmap (fun _ : Int => Finset VoteMsg)) : Prop where
  keys : Finmap.keys msgs = Finset.Icc 0 s.MaxRound
  typed : ∀ r ∈ Finset.Icc 0 s.MaxRound,
    ∀ m ∈ Finmap.lookupD r msgs, m ∈ precommit_universe s
  round : ∀ r ∈ Finmap.keys msgs,
    ∀ m ∈ Finmap.lookupD r msgs, r = m.round

lemma TypeComponents.proposal_map_facts {s : State} (h : TypeComponents s) :
    ProposalMapFacts s s.msgs_propose :=
  ⟨h.proposal_keys, h.proposals_typed, h.proposals_round⟩

lemma TypeComponents.prevote_map_facts {s : State} (h : TypeComponents s) :
    PrevoteMapFacts s s.msgs_prevote :=
  ⟨h.prevote_keys, h.prevotes_typed, h.prevotes_round⟩

lemma TypeComponents.precommit_map_facts {s : State} (h : TypeComponents s) :
    PrecommitMapFacts s s.msgs_precommit :=
  ⟨h.precommit_keys, h.precommits_typed, h.precommits_round⟩

lemma insert_proposal_map_facts {s : State}
    {msgs : Finmap (fun _ : Int => Finset ProposalMsg)}
    (h : ProposalMapFacts s msgs) {r : Int}
    (hr : r ∈ Finset.Icc 0 s.MaxRound) {added : Finset ProposalMsg}
    (htyped : ∀ m ∈ added, m ∈ proposal_universe s)
    (hround : ∀ m ∈ added, r = m.round) :
    ProposalMapFacts s
      (Finmap.insert r (Finmap.lookupD r msgs ∪ added) msgs) := by
  constructor
  · exact finmap_keys_insert_of_mem h.keys hr
  · intro k hk m hm
    by_cases hkr : k = r
    · subst k
      simp only [lookupD_insert_self, Finset.mem_union] at hm
      exact hm.elim (h.typed r hr m) (htyped m)
    · rw [lookupD_insert_of_ne hkr] at hm
      exact h.typed k hk m hm
  · intro k hk m hm
    have hkRange : k ∈ Finset.Icc 0 s.MaxRound := by
      rw [finmap_keys_insert_of_mem h.keys hr] at hk
      exact hk
    by_cases hkr : k = r
    · subst k
      simp only [lookupD_insert_self, Finset.mem_union] at hm
      exact hm.elim
        (h.round r (by simpa [h.keys] using hr) m)
        (hround m)
    · rw [lookupD_insert_of_ne hkr] at hm
      exact h.round k (by simpa [h.keys] using hkRange) m hm

lemma insert_prevote_map_facts {s : State}
    {msgs : Finmap (fun _ : Int => Finset VoteMsg)}
    (h : PrevoteMapFacts s msgs) {r : Int}
    (hr : r ∈ Finset.Icc 0 s.MaxRound) {added : Finset VoteMsg}
    (htyped : ∀ m ∈ added, m ∈ prevote_universe s)
    (hround : ∀ m ∈ added, r = m.round) :
    PrevoteMapFacts s
      (Finmap.insert r (Finmap.lookupD r msgs ∪ added) msgs) := by
  constructor
  · exact finmap_keys_insert_of_mem h.keys hr
  · intro k hk m hm
    by_cases hkr : k = r
    · subst k
      simp only [lookupD_insert_self, Finset.mem_union] at hm
      exact hm.elim (h.typed r hr m) (htyped m)
    · rw [lookupD_insert_of_ne hkr] at hm
      exact h.typed k hk m hm
  · intro k hk m hm
    have hkRange : k ∈ Finset.Icc 0 s.MaxRound := by
      rw [finmap_keys_insert_of_mem h.keys hr] at hk
      exact hk
    by_cases hkr : k = r
    · subst k
      simp only [lookupD_insert_self, Finset.mem_union] at hm
      exact hm.elim
        (h.round r (by simpa [h.keys] using hr) m)
        (hround m)
    · rw [lookupD_insert_of_ne hkr] at hm
      exact h.round k (by simpa [h.keys] using hkRange) m hm

lemma insert_precommit_map_facts {s : State}
    {msgs : Finmap (fun _ : Int => Finset VoteMsg)}
    (h : PrecommitMapFacts s msgs) {r : Int}
    (hr : r ∈ Finset.Icc 0 s.MaxRound) {added : Finset VoteMsg}
    (htyped : ∀ m ∈ added, m ∈ precommit_universe s)
    (hround : ∀ m ∈ added, r = m.round) :
    PrecommitMapFacts s
      (Finmap.insert r (Finmap.lookupD r msgs ∪ added) msgs) := by
  constructor
  · exact finmap_keys_insert_of_mem h.keys hr
  · intro k hk m hm
    by_cases hkr : k = r
    · subst k
      simp only [lookupD_insert_self, Finset.mem_union] at hm
      exact hm.elim (h.typed r hr m) (htyped m)
    · rw [lookupD_insert_of_ne hkr] at hm
      exact h.typed k hk m hm
  · intro k hk m hm
    have hkRange : k ∈ Finset.Icc 0 s.MaxRound := by
      rw [finmap_keys_insert_of_mem h.keys hr] at hk
      exact hk
    by_cases hkr : k = r
    · subst k
      simp only [lookupD_insert_self, Finset.mem_union] at hm
      exact hm.elim
        (h.round r (by simpa [h.keys] using hr) m)
        (hround m)
    · rw [lookupD_insert_of_ne hkr] at hm
      exact h.round k (by simpa [h.keys] using hkRange) m hm

lemma type_components_of_updates {s s' : State}
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hValid : s'.ValidValues = s.ValidValues)
    (hInvalid : s'.InvalidValues = s.InvalidValues)
    (hMax : s'.MaxRound = s.MaxRound)
    (hroundKeys : Finmap.keys s'.round = s.Corr)
    (hroundValues : ∀ p ∈ s.Corr,
      Finmap.lookupD p s'.round ∈ Finset.Icc 0 s.MaxRound)
    (hstepKeys : Finmap.keys s'.step = s.Corr)
    (hstepValues : ∀ p ∈ s.Corr,
      Finmap.lookupD p s'.step ∈
        insert Step.PROPOSE
          (insert Step.PREVOTE
            (insert Step.PRECOMMIT
              (insert Step.DECIDED (∅ : Finset Step)))))
    (hdecisionKeys : Finmap.keys s'.decision = s.Corr)
    (hdecisionValues : ∀ p ∈ s.Corr,
      Finmap.lookupD p s'.decision ∈ s.ValidValues ∪ insert (-1) ∅)
    (hlockedValueKeys : Finmap.keys s'.locked_value = s.Corr)
    (hlockedValues : ∀ p ∈ s.Corr,
      Finmap.lookupD p s'.locked_value ∈ s.ValidValues ∪ insert (-1) ∅)
    (hlockedRoundKeys : Finmap.keys s'.locked_round = s.Corr)
    (hlockedRounds : ∀ p ∈ s.Corr,
      Finmap.lookupD p s'.locked_round ∈
        Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅)
    (hvalidValueKeys : Finmap.keys s'.valid_value = s.Corr)
    (hvalidValues : ∀ p ∈ s.Corr,
      Finmap.lookupD p s'.valid_value ∈ s.ValidValues ∪ insert (-1) ∅)
    (hvalidRoundKeys : Finmap.keys s'.valid_round = s.Corr)
    (hvalidRounds : ∀ p ∈ s.Corr,
      Finmap.lookupD p s'.valid_round ∈
        Finset.Icc 0 s.MaxRound ∪ insert (-1) ∅)
    (hproposal : ProposalMapFacts s s'.msgs_propose)
    (hprevote : PrevoteMapFacts s s'.msgs_prevote)
    (hprecommit : PrecommitMapFacts s s'.msgs_precommit)
    (haction : s'.last_action ∈ action_labels) :
    TypeComponents s' := by
  refine
    { round_keys := by simpa [hCorr] using hroundKeys
      round_values := by simpa [hCorr, hMax] using hroundValues
      step_keys := by simpa [hCorr] using hstepKeys
      step_values := by simpa [hCorr] using hstepValues
      decision_keys := by simpa [hCorr] using hdecisionKeys
      decision_values := by
        simpa [hCorr, hValid] using hdecisionValues
      locked_value_keys := by simpa [hCorr] using hlockedValueKeys
      locked_values := by simpa [hCorr, hValid] using hlockedValues
      locked_round_keys := by simpa [hCorr] using hlockedRoundKeys
      locked_rounds := by simpa [hCorr, hMax] using hlockedRounds
      valid_value_keys := by simpa [hCorr] using hvalidValueKeys
      valid_values := by simpa [hCorr, hValid] using hvalidValues
      valid_round_keys := by simpa [hCorr] using hvalidRoundKeys
      valid_rounds := by simpa [hCorr, hMax] using hvalidRounds
      proposal_keys := by simpa [hMax] using hproposal.keys
      proposals_typed := by
        simpa [proposal_universe, hCorr, hFaulty, hValid, hInvalid, hMax]
          using hproposal.typed
      proposals_round := hproposal.round
      prevote_keys := by simpa [hMax] using hprevote.keys
      prevotes_typed := by
        simpa [prevote_universe, hCorr, hFaulty, hValid, hInvalid, hMax]
          using hprevote.typed
      prevotes_round := hprevote.round
      precommit_keys := by simpa [hMax] using hprecommit.keys
      precommits_typed := by
        simpa [precommit_universe, hCorr, hFaulty, hValid, hInvalid, hMax]
          using hprecommit.typed
      precommits_round := hprecommit.round
      action_typed := haction }

lemma precommit_value_messages_card_eq_pc_set {s : State}
    (htype : ind_type_ok s) {r value : Int}
    (hr : r ∈ Finset.Icc 0 s.MaxRound) :
    (Finset.filter (fun m => value = m.id)
        (Finmap.lookupD r s.msgs_precommit)).card =
      (pc_set s r value).card := by
  let msgs :=
    Finset.filter (fun m => value = m.id)
      (Finmap.lookupD r s.msgs_precommit)
  have ht := (ind_type_ok_iff_components s).mp htype
  have hrkey : r ∈ Finmap.keys s.msgs_precommit := by
    rw [ht.precommit_keys]
    exact hr
  have hmessage_fields :
      ∀ m ∈ msgs,
        m.kind = VoteKind.PRECOMMIT ∧ m.round = r ∧
          m.src ∈ all_replicas s := by
    intro m hm
    have hmLog := (Finset.mem_filter.mp hm).1
    have hmTyped := ht.precommits_typed r hr m hmLog
    unfold precommit_universe at hmTyped
    rcases Finset.mem_image.mp hmTyped with ⟨x, hx, hxeq⟩
    have hxsrc := (Finset.mem_product.mp hx).1
    have hmRound := ht.precommits_round r hrkey m hmLog
    subst m
    exact ⟨rfl, by simpa using hmRound.symm, hxsrc⟩
  have hinj : Set.InjOn VoteMsg.src msgs := by
    intro m₁ hm₁ m₂ hm₂ hsrc
    have hid₁ := (Finset.mem_filter.mp hm₁).2
    have hid₂ := (Finset.mem_filter.mp hm₂).2
    have hf₁ := hmessage_fields m₁ hm₁
    have hf₂ := hmessage_fields m₂ hm₂
    cases m₁
    cases m₂
    simp_all
  have himage :
      Finset.image VoteMsg.src msgs = pc_set s r value := by
    unfold pc_set vote_senders votes_for
    ext src
    constructor
    · intro hsrc
      rcases Finset.mem_image.mp hsrc with ⟨m, hm, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨(hmessage_fields m hm).2.2, m, hm, rfl⟩
    · intro hsrc
      rcases Finset.mem_filter.mp hsrc with ⟨_, m, hm, hsource⟩
      apply Finset.mem_image.mpr
      exact ⟨m, hm, hsource.symm⟩
  change msgs.card = (pc_set s r value).card
  rw [← himage, Finset.card_image_of_injOn hinj]

lemma prevote_value_messages_card_eq_pv_set {s : State}
    (htype : ind_type_ok s) {r value : Int}
    (hr : r ∈ Finset.Icc 0 s.MaxRound) :
    (Finset.filter (fun m => value = m.id)
        (Finmap.lookupD r s.msgs_prevote)).card =
      (pv_set s r value).card := by
  let msgs :=
    Finset.filter (fun m => value = m.id)
      (Finmap.lookupD r s.msgs_prevote)
  have ht := (ind_type_ok_iff_components s).mp htype
  have hrkey : r ∈ Finmap.keys s.msgs_prevote := by
    rw [ht.prevote_keys]
    exact hr
  have hmessage_fields :
      ∀ m ∈ msgs,
        m.kind = VoteKind.PREVOTE ∧ m.round = r ∧
          m.src ∈ all_replicas s := by
    intro m hm
    have hmLog := (Finset.mem_filter.mp hm).1
    have hmTyped := ht.prevotes_typed r hr m hmLog
    unfold prevote_universe at hmTyped
    rcases Finset.mem_image.mp hmTyped with ⟨x, hx, hxeq⟩
    have hxsrc := (Finset.mem_product.mp hx).1
    have hmRound := ht.prevotes_round r hrkey m hmLog
    subst m
    exact ⟨rfl, by simpa using hmRound.symm, hxsrc⟩
  have hinj : Set.InjOn VoteMsg.src msgs := by
    intro m₁ hm₁ m₂ hm₂ hsrc
    have hid₁ := (Finset.mem_filter.mp hm₁).2
    have hid₂ := (Finset.mem_filter.mp hm₂).2
    have hf₁ := hmessage_fields m₁ hm₁
    have hf₂ := hmessage_fields m₂ hm₂
    cases m₁
    cases m₂
    simp_all
  have himage :
      Finset.image VoteMsg.src msgs = pv_set s r value := by
    unfold pv_set vote_senders votes_for
    ext src
    constructor
    · intro hsrc
      rcases Finset.mem_image.mp hsrc with ⟨m, hm, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨(hmessage_fields m hm).2.2, m, hm, rfl⟩
    · intro hsrc
      rcases Finset.mem_filter.mp hsrc with ⟨_, m, hm, hsource⟩
      apply Finset.mem_image.mpr
      exact ⟨m, hm, hsource.symm⟩
  change msgs.card = (pv_set s r value).card
  rw [← himage, Finset.card_image_of_injOn hinj]

@[simp] lemma vote_senders_subset (s : State) (msgs : Finset VoteMsg) :
    vote_senders s msgs ⊆ all_replicas s := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

lemma vote_senders_mono_frame {s s' : State}
    {msgs msgs' : Finset VoteMsg}
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hsub : msgs ⊆ msgs') :
    vote_senders s msgs ⊆ vote_senders s' msgs' := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hall, m, hm, hsrc⟩
  apply Finset.mem_filter.mpr
  exact ⟨by simpa [all_replicas, hCorr, hFaulty] using hall,
    m, hsub hm, hsrc⟩

lemma pc_set_mono_frame {s s' : State} {r v : Int}
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hmsgs :
      Finmap.lookupD r s.msgs_precommit ⊆
        Finmap.lookupD r s'.msgs_precommit) :
    pc_set s r v ⊆ pc_set s' r v := by
  apply vote_senders_mono_frame hCorr hFaulty
  intro m hm
  exact Finset.mem_filter.mpr
    ⟨hmsgs (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩

lemma pv_set_mono_frame {s s' : State} {r v : Int}
    (hCorr : s'.Corr = s.Corr) (hFaulty : s'.Faulty = s.Faulty)
    (hmsgs :
      Finmap.lookupD r s.msgs_prevote ⊆
        Finmap.lookupD r s'.msgs_prevote) :
    pv_set s r v ⊆ pv_set s' r v := by
  apply vote_senders_mono_frame hCorr hFaulty
  intro m hm
  exact Finset.mem_filter.mpr
    ⟨hmsgs (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩

lemma mem_pv_set {s : State} {r v p : Int} :
    p ∈ pv_set s r v ↔
      p ∈ all_replicas s ∧
        ∃ m ∈ Finmap.lookupD r s.msgs_prevote, v = m.id ∧ p = m.src := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hall, m, hm, hsrc⟩
    exact ⟨hall, m, (Finset.mem_filter.mp hm).1,
      (Finset.mem_filter.mp hm).2, hsrc⟩
  · rintro ⟨hall, m, hm, hid, hsrc⟩
    exact Finset.mem_filter.mpr
      ⟨hall, m, Finset.mem_filter.mpr ⟨hm, hid⟩, hsrc⟩

lemma mem_pc_set {s : State} {r v p : Int} :
    p ∈ pc_set s r v ↔
      p ∈ all_replicas s ∧
        ∃ m ∈ Finmap.lookupD r s.msgs_precommit, v = m.id ∧ p = m.src := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hall, m, hm, hsrc⟩
    exact ⟨hall, m, (Finset.mem_filter.mp hm).1,
      (Finset.mem_filter.mp hm).2, hsrc⟩
  · rintro ⟨hall, m, hm, hid, hsrc⟩
    exact Finset.mem_filter.mpr
      ⟨hall, m, Finset.mem_filter.mpr ⟨hm, hid⟩, hsrc⟩

lemma card_all_replicas {s : State} (hmodel : model_assumptions s) :
    (all_replicas s).card = s.N := by
  unfold model_assumptions at hmodel
  rcases hmodel with ⟨_, _, _, hdisj, hcard, _⟩
  unfold all_replicas
  have hunion :=
    Finset.card_union_add_card_inter s.Corr s.Faulty
  rw [hdisj] at hunion
  simp only [Finset.card_empty, add_zero] at hunion
  omega

/-- Section A of the TLAPS proof: two `2T+1` quorums meet in a correct
replica under `N = 3T+1` and `|Faulty| ≤ T`. -/
theorem quorums_intersect_in_correct {s : State} (hmodel : model_assumptions s)
    {A B : Finset Int}
    (hAsub : A ⊆ all_replicas s) (hBsub : B ⊆ all_replicas s)
    (hAcard : (A.card : Int) ≥ 2 * s.T + 1)
    (hBcard : (B.card : Int) ≥ 2 * s.T + 1) :
    ∃ c ∈ s.Corr, c ∈ A ∧ c ∈ B := by
  by_contra hnone
  push_neg at hnone
  have hinter_sub : A ∩ B ⊆ s.Faulty := by
    intro x hx
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
    have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
    have hxall : x ∈ all_replicas s := hAsub hxA
    rcases Finset.mem_union.mp hxall with hcorr | hfaulty
    · exact (hnone x hcorr hxA hxB).elim
    · exact hfaulty
  have hinter_card_nat : (A ∩ B).card ≤ s.Faulty.card :=
    Finset.card_le_card hinter_sub
  have hunion_sub : A ∪ B ⊆ all_replicas s :=
    Finset.union_subset hAsub hBsub
  have hunion_card_nat : (A ∪ B).card ≤ (all_replicas s).card :=
    Finset.card_le_card hunion_sub
  have hinclusion := Finset.card_union_add_card_inter A B
  have hallcard := card_all_replicas hmodel
  unfold model_assumptions at hmodel
  rcases hmodel with ⟨_, hN, hfault, _⟩
  omega

theorem quorum_has_correct {s : State} (hmodel : model_assumptions s)
    {A : Finset Int} (hAsub : A ⊆ all_replicas s)
    (hAcard : (A.card : Int) ≥ 2 * s.T + 1) :
    ∃ c ∈ s.Corr, c ∈ A := by
  obtain ⟨c, hc, hcA, _⟩ :=
    quorums_intersect_in_correct hmodel hAsub hAsub hAcard hAcard
  exact ⟨c, hc, hcA⟩

lemma typed_ind_inv_iff (s : State) :
    typed_ind_inv s ↔ ind_type_ok s ∧ ind_inv s := by
  rfl

lemma foldl_max_zero (xs : List Int) (hzero : ∀ x ∈ xs, x = 0) :
    List.foldl (fun acc x => if x > acc then x else acc) 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : x = 0 := hzero x (by simp)
      subst x
      simp only [List.foldl_cons, gt_iff_lt, lt_self_iff_false, ↓reduceIte]
      apply ih
      intro y hy
      exact hzero y (by simp [hy])

lemma ind_inv_iff_named (s : State) :
    ind_inv s ↔
      all_no_future_messages_sent s ∧
        all_if_in_prevote_then_sent_prevote s ∧
          all_if_in_precommit_then_sent_precommit s ∧
            all_if_in_decided_then_received_proposal s ∧
              all_if_in_decided_then_received_two_thirds s ∧
                all_if_in_decided_then_valid_decision s ∧
                  all_locked_round_iff_locked_value s ∧
                    all_valid_round_iff_valid_value s ∧
                      all_valid_and_locked_round_bounded s ∧
                        all_if_valid_round_then_two_thirds_prevotes s ∧
                          all_if_locked_round_then_sent_commit s ∧
                            all_latest_precommit_has_locked_round s ∧
                              all_if_sent_prevote_then_received_proposal_or_two_thirds s ∧
                                if_sent_precommit_then_sent_prevote s ∧
                                  if_sent_precommit_then_received_two_thirds s ∧
                                    all_no_equivocation_by_correct s ∧
                                      precommits_lock_value s ∧
                                        precommit_locks_later_prevotes s ∧
                                          all_locked_proposer_reproposes s ∧
                                            all_past_start_round s ∧
                                              all_rounds_below_have_precommit_quorum s ∧
                                                all_valid_in_current_round_precommitted s ∧
                                                  all_locked_round_below_valid_round s ∧
                                                    all_if_valid_round_then_precommitted s ∧
                                                      all_correct_proposal_valid_round_below_round s := by
  rfl

lemma next_same_parameters {s s' : State} (hnext : Next s s') :
    same_parameters s s' := by
  unfold Next step at hnext
  rcases hnext with hfaulty | ⟨_, p, _, hcorrect⟩
  · unfold faulty_step at hfaulty
    rcases hfaulty with ⟨_, _, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
    unfold same_parameters
    exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
  · rcases hcorrect with h | h | h | h | h | h | h | h | h | h
    · unfold insert_proposal at h
      rcases h with ⟨_, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
    · unfold upon_proposal_in_propose at h
      rcases h with ⟨_, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
    · unfold upon_proposal_in_propose_and_prevote at h
      rcases h with ⟨_, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
    · unfold upon_quorum_of_prevotes_any at h
      rcases h with ⟨_, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
    · unfold upon_proposal_in_prevote_or_commit_and_prevote at h
      rcases h with ⟨_, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
    · unfold upon_quorum_of_precommits_any at h
      rcases h with ⟨_, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
    · unfold upon_proposal_in_precommit_no_decision at h
      rcases h with ⟨_, _, _, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
    · unfold on_timeout_propose at h
      rcases h with ⟨_, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
    · unfold on_quorum_of_nil_prevotes at h
      rcases h with ⟨_, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩
    · unfold on_round_catchup at h
      rcases h with ⟨_, _, hc, hf, hn, ht, hv, hi, hm, hp, _⟩
      unfold same_parameters
      exact ⟨hc, hf, hn, ht, hv, hi, hm, hp⟩

lemma next_preserves_model_assumptions {s s' : State}
    (hmodel : model_assumptions s) (hnext : Next s s') :
    model_assumptions s' := by
  have hframe := next_same_parameters hnext
  unfold same_parameters at hframe
  unfold model_assumptions at hmodel ⊢
  aesop

end tendermint_single_indinv
