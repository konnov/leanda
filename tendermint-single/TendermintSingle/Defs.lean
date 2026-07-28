-- Auto-generated from tendermint_single_indinv_ast.lean by ws_lean (Step B).
import TendermintSingle.Prelude

namespace tendermint_single_indinv

inductive Step where
  | PROPOSE
  | PREVOTE
  | PRECOMMIT
  | DECIDED
  deriving DecidableEq, Repr, Inhabited

inductive VoteKind where
  | PREVOTE
  | PRECOMMIT
  deriving DecidableEq, Repr, Inhabited

structure ProposalMsg where
  proposal : Int
  round : Int
  src : Int
  valid_round : Int
  deriving Inhabited

structure VoteMsg where
  id : Int
  kind : VoteKind
  round : Int
  src : Int
  deriving Inhabited

structure State where
  Corr : Finset Int
  Faulty : Finset Int
  N : Int
  T : Int
  ValidValues : Finset Int
  InvalidValues : Finset Int
  MaxRound : Int
  Proposer : Finmap (fun _ : Int => Int)
  round : Finmap (fun _ : Int => Int)
  step : Finmap (fun _ : Int => Step)
  decision : Finmap (fun _ : Int => Int)
  locked_value : Finmap (fun _ : Int => Int)
  locked_round : Finmap (fun _ : Int => Int)
  valid_value : Finmap (fun _ : Int => Int)
  valid_round : Finmap (fun _ : Int => Int)
  msgs_propose : Finmap (fun _ : Int => Finset ProposalMsg)
  msgs_prevote : Finmap (fun _ : Int => Finset VoteMsg)
  msgs_precommit : Finmap (fun _ : Int => Finset VoteMsg)
  last_action : String

def Wf (s : State) : Prop :=
  ws_and [Finmap.keys s.round = s.Corr, Finmap.keys s.step = s.Corr, Finmap.keys s.decision = s.Corr,
    Finmap.keys s.locked_value = s.Corr, Finmap.keys s.locked_round = s.Corr, Finmap.keys s.valid_value = s.Corr,
    Finmap.keys s.valid_round = s.Corr, Finmap.keys s.msgs_propose = Finset.Icc 0 s.MaxRound,
    Finmap.keys s.msgs_prevote = Finset.Icc 0 s.MaxRound, Finmap.keys s.msgs_precommit = Finset.Icc 0 s.MaxRound]

def all_no_future_messages_sent (s : State) : Prop :=
  ∀ _v104 ∈ s.Corr,
    ws_and [ws_and [_v104 = Finmap.lookupD (Finmap.lookupD _v104 s.round) s.Proposer ∨
          ∀ _v105 ∈ Finmap.lookupD (Finmap.lookupD _v104 s.round) s.msgs_propose, _v104 ≠ ProposalMsg.src _v105,
        Finmap.lookupD _v104 s.step = Step.PREVOTE ∨
          Finmap.lookupD _v104 s.step = Step.PRECOMMIT ∨
            Finmap.lookupD _v104 s.step = Step.DECIDED ∨
              ∀ _v106 ∈ Finmap.lookupD (Finmap.lookupD _v104 s.round) s.msgs_prevote, _v104 ≠ VoteMsg.src _v106,
        Finmap.lookupD _v104 s.step = Step.PRECOMMIT ∨
          Finmap.lookupD _v104 s.step = Step.DECIDED ∨
            ∀ _v107 ∈ Finmap.lookupD (Finmap.lookupD _v104 s.round) s.msgs_precommit, _v104 ≠ VoteMsg.src _v107],
      ∀ _v109 ∈ Finset.filter (fun _v108 => _v108 > Finmap.lookupD _v104 s.round) (Finset.Icc 0 s.MaxRound),
        ws_and [∀ _v110 ∈ Finmap.lookupD _v109 s.msgs_propose, _v104 ≠ ProposalMsg.src _v110,
          ∀ _v111 ∈ Finmap.lookupD _v109 s.msgs_prevote, _v104 ≠ VoteMsg.src _v111,
          ∀ _v112 ∈ Finmap.lookupD _v109 s.msgs_precommit, _v104 ≠ VoteMsg.src _v112]]

def all_if_in_prevote_then_sent_prevote (s : State) : Prop :=
  ∀ _v113 ∈ s.Corr,
    Finmap.lookupD _v113 s.step = Step.PREVOTE →
      ∃ _v114 ∈ Finmap.lookupD (Finmap.lookupD _v113 s.round) s.msgs_prevote,
        ws_and [VoteMsg.id _v114 ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) (∅ : Finset Int),
          _v113 = VoteMsg.src _v114]

def all_if_in_precommit_then_sent_precommit (s : State) : Prop :=
  ∀ _v115 ∈ s.Corr,
    Finmap.lookupD _v115 s.step = Step.PRECOMMIT →
      ∃ _v116 ∈ Finmap.lookupD (Finmap.lookupD _v115 s.round) s.msgs_precommit,
        ws_and [VoteMsg.id _v116 ∈ s.ValidValues ∪ s.InvalidValues ∪ insert (-1) (∅ : Finset Int),
          _v115 = VoteMsg.src _v116]

def all_if_in_decided_then_received_proposal (s : State) : Prop :=
  ∀ _v117 ∈ s.Corr,
    Finmap.lookupD _v117 s.step = Step.DECIDED →
      ∃ _v118 ∈ Finset.Icc 0 s.MaxRound,
        ∃ _v119 ∈ Finmap.lookupD _v118 s.msgs_propose,
          ws_and [ProposalMsg.src _v119 = Finmap.lookupD _v118 s.Proposer,
            ProposalMsg.proposal _v119 = Finmap.lookupD _v117 s.decision]

def all_if_in_decided_then_received_two_thirds (s : State) : Prop :=
  ∀ _v120 ∈ s.Corr,
    Finmap.lookupD _v120 s.step = Step.DECIDED →
      ∃ _v121 ∈ Finset.Icc 0 s.MaxRound,
        Finset.card
            (Finset.filter
              (fun _v123 =>
                ∃
                  _v124 ∈
                    Finset.filter (fun _v122 => VoteMsg.id _v122 = Finmap.lookupD _v120 s.decision)
                      (Finmap.lookupD _v121 s.msgs_precommit),
                  _v123 = VoteMsg.src _v124)
              (s.Corr ∪ s.Faulty)) ≥
          2 * s.T + 1

def all_if_in_decided_then_valid_decision (s : State) : Prop :=
  ∀ _v125 ∈ s.Corr, (Finmap.lookupD _v125 s.step = Step.DECIDED) = (Finmap.lookupD _v125 s.decision ∈ s.ValidValues)

def all_locked_round_iff_locked_value (s : State) : Prop :=
  ∀ _v126 ∈ s.Corr, (Finmap.lookupD _v126 s.locked_round = -1) = (Finmap.lookupD _v126 s.locked_value = -1)

def all_valid_round_iff_valid_value (s : State) : Prop :=
  ∀ _v127 ∈ s.Corr, (Finmap.lookupD _v127 s.valid_round = -1) = (Finmap.lookupD _v127 s.valid_value = -1)

def all_valid_and_locked_round_bounded (s : State) : Prop :=
  ∀ _v128 ∈ s.Corr,
    ws_and [Finmap.lookupD _v128 s.valid_round ≤ Finmap.lookupD _v128 s.round,
      Finmap.lookupD _v128 s.locked_round ≤ Finmap.lookupD _v128 s.round]

def all_if_valid_round_then_two_thirds_prevotes (s : State) : Prop :=
  ∀ _v129 ∈ s.Corr,
    Finmap.lookupD _v129 s.valid_round ≠ -1 →
      Finset.card
          (Finset.filter
            (fun _v131 =>
              ∃
                _v132 ∈
                  Finset.filter (fun _v130 => VoteMsg.id _v130 = Finmap.lookupD _v129 s.valid_value)
                    (Finmap.lookupD (Finmap.lookupD _v129 s.valid_round) s.msgs_prevote),
                _v131 = VoteMsg.src _v132)
            (s.Corr ∪ s.Faulty)) ≥
        2 * s.T + 1

def all_if_locked_round_then_sent_commit (s : State) : Prop :=
  ∀ _v133 ∈ s.Corr,
    Finmap.lookupD _v133 s.locked_round ≠ -1 →
      ∃ _v134 ∈ Finset.Icc 0 s.MaxRound,
        ws_and [_v134 ≤ Finmap.lookupD _v133 s.round,
          ∃ _v135 ∈ Finmap.lookupD _v134 s.msgs_precommit,
            ws_and [_v133 = VoteMsg.src _v135, VoteMsg.id _v135 = Finmap.lookupD _v133 s.locked_value]]

def all_latest_precommit_has_locked_round (s : State) : Prop :=
  ∀ _v136 ∈ s.Corr,
    ws_and [Finmap.lookupD _v136 s.locked_round = -1, Finmap.lookupD _v136 s.locked_value = -1,
        ∀ _v137 ∈ Finset.Icc 0 s.MaxRound,
          ∀ _v138 ∈ Finmap.lookupD _v137 s.msgs_precommit, _v136 ≠ VoteMsg.src _v138 ∨ VoteMsg.id _v138 = -1] ∨
      ws_and [Finmap.lookupD _v136 s.locked_round ≠ -1, Finmap.lookupD _v136 s.locked_value ≠ -1,
        ∀ _v139 ∈ Finset.Icc 0 s.MaxRound,
          ∀ _v140 ∈ Finmap.lookupD _v139 s.msgs_precommit,
            (_v136 ≠ VoteMsg.src _v140 ∨ VoteMsg.round _v140 ≤ Finmap.lookupD _v136 s.locked_round) ∨
              VoteMsg.id _v140 = -1,
        ∃ _v141 ∈ Finmap.lookupD (Finmap.lookupD _v136 s.locked_round) s.msgs_precommit,
          ws_and [_v136 = VoteMsg.src _v141, VoteMsg.id _v141 = Finmap.lookupD _v136 s.locked_value]]

def all_if_sent_prevote_then_received_proposal_or_two_thirds (s : State) : Prop :=
  ∀ _v142 ∈ Finset.Icc 0 s.MaxRound,
    ∀ _v143 ∈ Finmap.lookupD _v142 s.msgs_prevote,
      VoteMsg.src _v143 ∈ s.Faulty ∨
        VoteMsg.id _v143 = -1 ∨
          ws_and [VoteMsg.id _v143 ≠ -1,
            (∃ _v144 ∈ Finmap.lookupD _v142 s.msgs_propose,
                ws_and [ProposalMsg.src _v144 = Finmap.lookupD _v142 s.Proposer,
                  ProposalMsg.proposal _v144 = VoteMsg.id _v143, ProposalMsg.valid_round _v144 = -1]) ∨
              ∃ _v146 ∈ Finset.filter (fun rr => rr < _v142) (Finset.Icc 0 s.MaxRound),
                ws_and [∃ _v147 ∈ Finmap.lookupD _v142 s.msgs_propose,
                    ws_and [ProposalMsg.src _v147 = Finmap.lookupD _v142 s.Proposer,
                      ProposalMsg.proposal _v147 = VoteMsg.id _v143, _v146 = ProposalMsg.valid_round _v147],
                  Finset.card
                      (Finset.filter
                        (fun _v149 =>
                          ∃
                            _v150 ∈
                              Finset.filter (fun _v148 => VoteMsg.id _v148 = VoteMsg.id _v143)
                                (Finmap.lookupD _v146 s.msgs_prevote),
                            _v149 = VoteMsg.src _v150)
                        (s.Corr ∪ s.Faulty)) ≥
                    2 * s.T + 1]]

def if_sent_precommit_then_sent_prevote (s : State) : Prop :=
  ∀ _v151 ∈ Finset.Icc 0 s.MaxRound,
    ∀ _v152 ∈ Finmap.lookupD _v151 s.msgs_precommit,
      VoteMsg.src _v152 ∈ s.Corr → ∃ _v153 ∈ Finmap.lookupD _v151 s.msgs_prevote, VoteMsg.src _v153 = VoteMsg.src _v152

def if_sent_precommit_then_received_two_thirds (s : State) : Prop :=
  ∀ _v154 ∈ Finset.Icc 0 s.MaxRound,
    ∀ _v155 ∈ Finmap.lookupD _v154 s.msgs_precommit,
      VoteMsg.src _v155 ∈ s.Corr →
        ws_and [VoteMsg.id _v155 ∈ s.ValidValues,
            Finset.card
                (Finset.filter
                  (fun _v157 =>
                    ∃
                      _v158 ∈
                        Finset.filter (fun _v156 => VoteMsg.id _v156 = VoteMsg.id _v155)
                          (Finmap.lookupD _v154 s.msgs_prevote),
                      _v157 = VoteMsg.src _v158)
                  (s.Corr ∪ s.Faulty)) ≥
              2 * s.T + 1] ∨
          ws_and [VoteMsg.id _v155 = -1,
            Finset.card
                (Finset.filter (fun _v159 => ∃ _v160 ∈ Finmap.lookupD _v154 s.msgs_prevote, _v159 = VoteMsg.src _v160)
                  (s.Corr ∪ s.Faulty)) ≥
              2 * s.T + 1]

def all_no_equivocation_by_correct (s : State) : Prop :=
  ∀ _v161 ∈ Finset.Icc 0 s.MaxRound,
    ws_and [∃ _v162 ∈ s.ValidValues,
        ∃ _v163 ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int),
          ∀ _v164 ∈ Finmap.lookupD _v161 s.msgs_propose,
            ProposalMsg.src _v164 ∈ s.Faulty ∨
              ws_and [ws_and [ProposalMsg.src _v164 = Finmap.lookupD _v161 s.Proposer,
                  _v162 = ProposalMsg.proposal _v164],
                _v163 = ProposalMsg.valid_round _v164],
      ∀ _v165 ∈ s.Corr,
        ∃ _v166 ∈ s.ValidValues ∪ insert (-1) (∅ : Finset Int),
          ∀ _v167 ∈ Finmap.lookupD _v161 s.msgs_prevote, _v165 = VoteMsg.src _v167 → _v166 = VoteMsg.id _v167,
      ∀ _v168 ∈ s.Corr,
        ∃ _v169 ∈ s.ValidValues ∪ insert (-1) (∅ : Finset Int),
          ∀ _v170 ∈ Finmap.lookupD _v161 s.msgs_precommit, _v168 = VoteMsg.src _v170 → _v169 = VoteMsg.id _v170]

def precommits_lock_value (s : State) : Prop :=
  ∀ _v171 ∈ Finset.Icc 0 s.MaxRound,
    ∀ _v172 ∈ s.ValidValues,
      Finset.card
            (Finset.filter
              (fun _v174 =>
                ∃ _v175 ∈ Finset.filter (fun _v173 => _v172 = VoteMsg.id _v173) (Finmap.lookupD _v171 s.msgs_precommit),
                  _v174 = VoteMsg.src _v175)
              (s.Corr ∪ s.Faulty)) <
          2 * s.T + 1 ∨
        ∀ _v177 ∈ Finset.filter (fun _v176 => _v176 > _v171) (Finset.Icc 0 s.MaxRound),
          ∀ _v178 ∈ s.ValidValues \ insert _v172 (∅ : Finset Int),
            Finset.card
                (Finset.filter
                  (fun _v180 =>
                    ∃
                      _v181 ∈
                        Finset.filter (fun _v179 => _v178 = VoteMsg.id _v179) (Finmap.lookupD _v177 s.msgs_prevote),
                      _v180 = VoteMsg.src _v181)
                  (s.Corr ∪ s.Faulty)) <
              2 * s.T + 1

-- Per-process support that makes precommits_lock_value inductive. If a correct
-- process precommitted a non-NIL value (!= w) in round r (locking it), then it
-- prevotes w in a later round r2 only if w reached a 2f+1 prevote quorum in some
-- round in [r, r2) -- the only way it could re-lock to w. Quantifiers range over
-- the small Corr/rounds/ValidValues domains; message pools appear only under
-- existentials, keeping the SMT encoding cheap.
def precommit_locks_later_prevotes (s : State) : Prop :=
  ∀ _v182 ∈ s.Corr,
    ∀ _v183 ∈ Finset.Icc 0 s.MaxRound,
      ∀ _v184 ∈ s.ValidValues,
        ∀ _v185 ∈ Finset.Icc 0 s.MaxRound,
          ws_and [_v185 > _v183,
              ∃ _v186 ∈ Finmap.lookupD _v183 s.msgs_precommit,
                ws_and [ws_and [_v182 = VoteMsg.src _v186, VoteMsg.id _v186 ≠ -1], _v184 ≠ VoteMsg.id _v186],
              ∃ _v187 ∈ Finmap.lookupD _v185 s.msgs_prevote,
                ws_and [_v182 = VoteMsg.src _v187, _v184 = VoteMsg.id _v187]] →
            ∃ _v189 ∈ Finset.filter (fun _v188 => ws_and [_v188 ≥ _v183, _v188 < _v185]) (Finset.Icc 0 s.MaxRound),
              Finset.card
                  (Finset.filter
                    (fun _v191 =>
                      ∃
                        _v192 ∈
                          Finset.filter (fun _v190 => _v184 = VoteMsg.id _v190) (Finmap.lookupD _v189 s.msgs_prevote),
                        _v191 = VoteMsg.src _v192)
                    (s.Corr ∪ s.Faulty)) ≥
                2 * s.T + 1

-- A correct proposer that already locked (precommitted a non-NIL value in an
-- earlier round) never sends a fresh proposal (valid_round == NIL): a non-NIL
-- precommit sets valid_value, which never reverts to NIL, so insert_proposal
-- re-proposes it with a non-NIL valid_round.
def all_locked_proposer_reproposes (s : State) : Prop :=
  ∀ _v193 ∈ Finset.Icc 0 s.MaxRound,
    ws_and [Finmap.lookupD _v193 s.Proposer ∈ s.Corr,
        ∃ _v194 ∈ Finmap.lookupD _v193 s.msgs_propose,
          ws_and [ProposalMsg.src _v194 = Finmap.lookupD _v193 s.Proposer, ProposalMsg.valid_round _v194 = -1]] →
      ∀ _v196 ∈ Finset.filter (fun _v195 => _v195 < _v193) (Finset.Icc 0 s.MaxRound),
        ¬∃ _v197 ∈ Finmap.lookupD _v196 s.msgs_precommit,
            ws_and [VoteMsg.src _v197 = Finmap.lookupD _v193 s.Proposer, VoteMsg.id _v197 ≠ -1]

-- To be in a round, requires StartRound in the past
def all_past_start_round (s : State) : Prop :=
  ∀ _v198 ∈ s.Corr,
    ∀ _v199 ∈ Finset.Icc 0 s.MaxRound,
      _v199 > Finmap.lookupD _v198 s.round ∨
        _v199 = 0 ∨
          Finset.card
                (Finset.filter (fun _v202 => ∃ _v203 ∈ Finmap.lookupD _v199 s.msgs_prevote, _v202 = VoteMsg.src _v203)
                    (s.Corr ∪ s.Faulty) ∪
                  Finset.filter
                    (fun _v200 => ∃ _v201 ∈ Finmap.lookupD _v199 s.msgs_precommit, _v200 = VoteMsg.src _v201)
                    (s.Corr ∪ s.Faulty)) ≥
              s.T + 1 ∨
            Finset.card
                (Finset.filter
                  (fun _v204 => ∃ _v205 ∈ Finmap.lookupD (_v199 - 1) s.msgs_precommit, _v204 = VoteMsg.src _v205)
                  (s.Corr ∪ s.Faulty)) ≥
              2 * s.T + 1

-- A correct process can only be in round r if every earlier round already
-- collected a 2f+1 precommit quorum (the only way the global maximum round
-- advances is upon_quorum_of_precommits_any, which needs 2f+1 precommits in
-- round r-1).
--
-- The inner constraint does not depend on the process, so instead of quantifying
-- over Corr we take the maximum round reached by any correct process and require
-- the quorum in every round strictly below it.
def all_rounds_below_have_precommit_quorum (s : State) : Prop :=
  ∀ _v209 ∈ Finset.Icc 0 s.MaxRound,
    _v209 <
        List.foldl (fun acc x => if x > acc then x else acc) 0
          (Finset.toList (Finset.image (fun k => Finmap.lookupD k s.round) (Finmap.keys s.round))) →
      Finset.card
          (Finset.filter (fun _v210 => ∃ _v211 ∈ Finmap.lookupD _v209 s.msgs_precommit, _v210 = VoteMsg.src _v211)
            (s.Corr ∪ s.Faulty)) ≥
        2 * s.T + 1

-- If a correct process set valid_round in the round it is still in, it has
-- already passed PREVOTE: valid_round is only assigned by
-- upon_proposal_in_prevote_or_commit_and_prevote (guard step PREVOTE/PRECOMMIT),
-- which leaves the process in step PRECOMMIT. A round is never revisited and the
-- step only advances within a round, so step must be PRECOMMIT or DECIDED.
-- valid_round == NIL never equals round >= 0, so the NIL case is vacuous.
def all_valid_in_current_round_precommitted (s : State) : Prop :=
  ∀ _v212 ∈ s.Corr,
    Finmap.lookupD _v212 s.valid_round = Finmap.lookupD _v212 s.round →
      Finmap.lookupD _v212 s.step = Step.PRECOMMIT ∨ Finmap.lookupD _v212 s.step = Step.DECIDED

-- locked_* and valid_* are set together when locking (the prevote branch of
-- upon_proposal_in_prevote_or_commit_and_prevote), and valid_round only advances
-- afterwards, so locked_round <= valid_round. NIL_ROUND = -1 makes the unlocked
-- case free and forces valid_round != NIL whenever the process is locked.
def all_locked_round_below_valid_round (s : State) : Prop :=
  ∀ _v213 ∈ s.Corr, Finmap.lookupD _v213 s.locked_round ≤ Finmap.lookupD _v213 s.valid_round

-- Setting valid_round = r requires reaching step PREVOTE/PRECOMMIT in round r,
-- after which the process has broadcast a precommit in round r (the prevote branch
-- precommits the value; the precommit branch means it already precommitted).
def all_if_valid_round_then_precommitted (s : State) : Prop :=
  ∀ _v214 ∈ s.Corr,
    Finmap.lookupD _v214 s.valid_round ≠ -1 →
      ∃ _v215 ∈ Finmap.lookupD (Finmap.lookupD _v214 s.valid_round) s.msgs_precommit, _v214 = VoteMsg.src _v215

-- A correct proposer broadcasts (insert_proposal) while in step PROPOSE, where
-- valid_round[p] < round[p] (it equals round only from PRECOMMIT on, and is
-- bounded by round). So every proposal from a correct src has valid_round < round.
def all_correct_proposal_valid_round_below_round (s : State) : Prop :=
  ∀ _v216 ∈ Finset.Icc 0 s.MaxRound,
    ∀ _v217 ∈ Finmap.lookupD _v216 s.msgs_propose,
      ProposalMsg.src _v217 ∈ s.Corr → _v216 > ProposalMsg.valid_round _v217

def ind_type_ok (s : State) : Prop :=
  ws_and [Finmap.keys s.round = s.Corr ∧ ∀ k0 ∈ s.Corr, Finmap.lookupD k0 s.round ∈ Finset.Icc 0 s.MaxRound,
    Finmap.keys s.step = s.Corr ∧
      ∀ k0 ∈ s.Corr,
        Finmap.lookupD k0 s.step ∈
          insert Step.PROPOSE (insert Step.PREVOTE (insert Step.PRECOMMIT (insert Step.DECIDED (∅ : Finset Step)))),
    Finmap.keys s.decision = s.Corr ∧
      ∀ k0 ∈ s.Corr, Finmap.lookupD k0 s.decision ∈ s.ValidValues ∪ insert (-1) (∅ : Finset Int),
    Finmap.keys s.locked_value = s.Corr ∧
      ∀ k0 ∈ s.Corr, Finmap.lookupD k0 s.locked_value ∈ s.ValidValues ∪ insert (-1) (∅ : Finset Int),
    Finmap.keys s.locked_round = s.Corr ∧
      ∀ k0 ∈ s.Corr, Finmap.lookupD k0 s.locked_round ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int),
    Finmap.keys s.valid_value = s.Corr ∧
      ∀ k0 ∈ s.Corr, Finmap.lookupD k0 s.valid_value ∈ s.ValidValues ∪ insert (-1) (∅ : Finset Int),
    Finmap.keys s.valid_round = s.Corr ∧
      ∀ k0 ∈ s.Corr, Finmap.lookupD k0 s.valid_round ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int),
    Finmap.keys s.msgs_propose = Finset.Icc 0 s.MaxRound,
    ∀ _v341 ∈ Finset.Icc 0 s.MaxRound,
      ∀ _v342 ∈ Finmap.lookupD _v341 s.msgs_propose,
        _v342 ∈
          Finset.image (fun _v343 => ProposalMsg.mk (((_v343).2).2).1 ((_v343).2).1 (_v343).1 (((_v343).2).2).2)
            (Finset.product (s.Corr ∪ s.Faulty)
              (Finset.product (Finset.Icc 0 s.MaxRound)
                (Finset.product (s.ValidValues ∪ s.InvalidValues ∪ insert (-1) (∅ : Finset Int))
                  (Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int))))),
    ∀ _v344 ∈ Finmap.keys s.msgs_propose,
      ∀ _v345 ∈ Finmap.lookupD _v344 s.msgs_propose, _v344 = ProposalMsg.round _v345,
    Finmap.keys s.msgs_prevote = Finset.Icc 0 s.MaxRound,
    ∀ _v346 ∈ Finset.Icc 0 s.MaxRound,
      ∀ _v347 ∈ Finmap.lookupD _v346 s.msgs_prevote,
        _v347 ∈
          Finset.image (fun _v348 => VoteMsg.mk ((_v348).2).2 VoteKind.PREVOTE ((_v348).2).1 (_v348).1)
            (Finset.product (s.Corr ∪ s.Faulty)
              (Finset.product (Finset.Icc 0 s.MaxRound)
                (s.ValidValues ∪ s.InvalidValues ∪ insert (-1) (∅ : Finset Int)))),
    ∀ _v349 ∈ Finmap.keys s.msgs_prevote, ∀ _v350 ∈ Finmap.lookupD _v349 s.msgs_prevote, _v349 = VoteMsg.round _v350,
    Finmap.keys s.msgs_precommit = Finset.Icc 0 s.MaxRound,
    ∀ _v351 ∈ Finset.Icc 0 s.MaxRound,
      ∀ _v352 ∈ Finmap.lookupD _v351 s.msgs_precommit,
        _v352 ∈
          Finset.image (fun _v353 => VoteMsg.mk ((_v353).2).2 VoteKind.PRECOMMIT ((_v353).2).1 (_v353).1)
            (Finset.product (s.Corr ∪ s.Faulty)
              (Finset.product (Finset.Icc 0 s.MaxRound)
                (s.ValidValues ∪ s.InvalidValues ∪ insert (-1) (∅ : Finset Int)))),
    ∀ _v354 ∈ Finmap.keys s.msgs_precommit,
      ∀ _v355 ∈ Finmap.lookupD _v354 s.msgs_precommit, _v354 = VoteMsg.round _v355,
    s.last_action ∈
      insert "INIT"
        (insert "INSERT_PROPOSAL"
          (insert "UPON_PROPOSAL_PROPOSE"
            (insert "UPON_PROPOSAL_PROPOSE_AND_PREVOTE"
              (insert "UPON_QUORUM_PREVOTES_ANY"
                (insert "UPON_PROPOSAL_PREVOTE_OR_COMMIT_AND_PREVOTE"
                  (insert "UPON_QUORUM_PRECOMMITS_ANY"
                    (insert "UPON_PROPOSAL_PRECOMMIT_NO_DECISION"
                      (insert "ON_TIMEOUT_PROPOSE"
                        (insert "ON_QUORUM_NIL_PREVOTES" (insert "ON_ROUND_CATCHUP" (∅ : Finset String)))))))))))]

def ind_inv (s : State) : Prop :=
  ws_and [all_no_future_messages_sent s, all_if_in_prevote_then_sent_prevote s,
    all_if_in_precommit_then_sent_precommit s, all_if_in_decided_then_received_proposal s,
    all_if_in_decided_then_received_two_thirds s, all_if_in_decided_then_valid_decision s,
    all_locked_round_iff_locked_value s, all_valid_round_iff_valid_value s, all_valid_and_locked_round_bounded s,
    all_if_valid_round_then_two_thirds_prevotes s, all_if_locked_round_then_sent_commit s,
    all_latest_precommit_has_locked_round s, all_if_sent_prevote_then_received_proposal_or_two_thirds s,
    if_sent_precommit_then_sent_prevote s, if_sent_precommit_then_received_two_thirds s,
    all_no_equivocation_by_correct s, precommits_lock_value s, precommit_locks_later_prevotes s,
    all_locked_proposer_reproposes s, all_past_start_round s, all_rounds_below_have_precommit_quorum s,
    all_valid_in_current_round_precommitted s, all_locked_round_below_valid_round s,
    all_if_valid_round_then_precommitted s, all_correct_proposal_valid_round_below_round s]

-- The Tendermint safety property: agreement among correct processes.
def agreement (s : State) : Prop :=
  ∀ _v86 ∈ s.Corr,
    ∀ _v87 ∈ s.Corr,
      (Finmap.lookupD _v86 s.decision = -1 ∨ Finmap.lookupD _v87 s.decision = -1) ∨
        Finmap.lookupD _v86 s.decision = Finmap.lookupD _v87 s.decision

-- Protocol validity: correct decisions are valid values or nil.
def validity (s : State) : Prop :=
  ∀ _v88 ∈ s.Corr, Finmap.lookupD _v88 s.decision = -1 ∨ Finmap.lookupD _v88 s.decision ∈ s.ValidValues

def typed_ind_inv (s : State) : Prop :=
  ws_and [ind_type_ok s, ind_inv s]

-- Algorithm 1, lines 1-9, adapted to one height.
-- This initializer starts with empty message logs for faulty processes.
def init (s : State) : Prop :=
  ws_and [Finmap.keys s.round = s.Corr, ∀ _v0 ∈ s.Corr, Finmap.lookupD _v0 s.round = 0, Finmap.keys s.step = s.Corr,
    ∀ _v1 ∈ s.Corr, Finmap.lookupD _v1 s.step = Step.PROPOSE, Finmap.keys s.decision = s.Corr,
    ∀ _v2 ∈ s.Corr, Finmap.lookupD _v2 s.decision = -1, Finmap.keys s.locked_value = s.Corr,
    ∀ _v3 ∈ s.Corr, Finmap.lookupD _v3 s.locked_value = -1, Finmap.keys s.locked_round = s.Corr,
    ∀ _v4 ∈ s.Corr, Finmap.lookupD _v4 s.locked_round = -1, Finmap.keys s.valid_value = s.Corr,
    ∀ _v5 ∈ s.Corr, Finmap.lookupD _v5 s.valid_value = -1, Finmap.keys s.valid_round = s.Corr,
    ∀ _v6 ∈ s.Corr, Finmap.lookupD _v6 s.valid_round = -1, Finmap.keys s.msgs_propose = Finset.Icc 0 s.MaxRound,
    ∀ _v7 ∈ Finset.Icc 0 s.MaxRound, Finmap.lookupD _v7 s.msgs_propose = (∅ : Finset ProposalMsg),
    Finmap.keys s.msgs_prevote = Finset.Icc 0 s.MaxRound,
    ∀ _v8 ∈ Finset.Icc 0 s.MaxRound, Finmap.lookupD _v8 s.msgs_prevote = (∅ : Finset VoteMsg),
    Finmap.keys s.msgs_precommit = Finset.Icc 0 s.MaxRound,
    ∀ _v9 ∈ Finset.Icc 0 s.MaxRound, Finmap.lookupD _v9 s.msgs_precommit = (∅ : Finset VoteMsg), s.last_action = "INIT"]

-- Algorithm 1, lines 1-9, adapted to one height.
-- Extension: the initial message logs may contain arbitrary faulty messages.
def init_with_faults (s : State) : Prop :=
  ws_and [Finset.powerset
        (Finset.image (fun _v10 => ProposalMsg.mk (((_v10).2).2).1 ((_v10).2).1 (_v10).1 (((_v10).2).2).2)
          (Finset.product s.Faulty
            (Finset.product (Finset.Icc 0 s.MaxRound)
              (Finset.product (s.ValidValues ∪ s.InvalidValues)
                (Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int)))))) ≠
      (∅ : Finset (Finset ProposalMsg)),
    ∃
      faulty_proposals ∈
        Finset.powerset
          (Finset.image (fun _v10 => ProposalMsg.mk (((_v10).2).2).1 ((_v10).2).1 (_v10).1 (((_v10).2).2).2)
            (Finset.product s.Faulty
              (Finset.product (Finset.Icc 0 s.MaxRound)
                (Finset.product (s.ValidValues ∪ s.InvalidValues)
                  (Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int)))))),
      ws_and [Finset.powerset
            (Finset.image (fun _v11 => VoteMsg.mk ((_v11).2).2 VoteKind.PREVOTE ((_v11).2).1 (_v11).1)
              (Finset.product s.Faulty (Finset.product (Finset.Icc 0 s.MaxRound) (s.ValidValues ∪ s.InvalidValues)))) ≠
          (∅ : Finset (Finset VoteMsg)),
        ∃
          faulty_prevotes ∈
            Finset.powerset
              (Finset.image (fun _v11 => VoteMsg.mk ((_v11).2).2 VoteKind.PREVOTE ((_v11).2).1 (_v11).1)
                (Finset.product s.Faulty (Finset.product (Finset.Icc 0 s.MaxRound) (s.ValidValues ∪ s.InvalidValues)))),
          ws_and [Finset.powerset
                (Finset.image (fun _v12 => VoteMsg.mk ((_v12).2).2 VoteKind.PRECOMMIT ((_v12).2).1 (_v12).1)
                  (Finset.product s.Faulty
                    (Finset.product (Finset.Icc 0 s.MaxRound) (s.ValidValues ∪ s.InvalidValues)))) ≠
              (∅ : Finset (Finset VoteMsg)),
            ∃
              faulty_precommits ∈
                Finset.powerset
                  (Finset.image (fun _v12 => VoteMsg.mk ((_v12).2).2 VoteKind.PRECOMMIT ((_v12).2).1 (_v12).1)
                    (Finset.product s.Faulty
                      (Finset.product (Finset.Icc 0 s.MaxRound) (s.ValidValues ∪ s.InvalidValues)))),
              ws_and [Finmap.keys s.round = s.Corr, ∀ _v13 ∈ s.Corr, Finmap.lookupD _v13 s.round = 0,
                Finmap.keys s.step = s.Corr, ∀ _v14 ∈ s.Corr, Finmap.lookupD _v14 s.step = Step.PROPOSE,
                Finmap.keys s.decision = s.Corr, ∀ _v15 ∈ s.Corr, Finmap.lookupD _v15 s.decision = -1,
                Finmap.keys s.locked_value = s.Corr, ∀ _v16 ∈ s.Corr, Finmap.lookupD _v16 s.locked_value = -1,
                Finmap.keys s.locked_round = s.Corr, ∀ _v17 ∈ s.Corr, Finmap.lookupD _v17 s.locked_round = -1,
                Finmap.keys s.valid_value = s.Corr, ∀ _v18 ∈ s.Corr, Finmap.lookupD _v18 s.valid_value = -1,
                Finmap.keys s.valid_round = s.Corr, ∀ _v19 ∈ s.Corr, Finmap.lookupD _v19 s.valid_round = -1,
                Finmap.keys s.msgs_propose = Finset.Icc 0 s.MaxRound,
                ∀ _v20 ∈ Finset.Icc 0 s.MaxRound,
                  Finmap.lookupD _v20 s.msgs_propose =
                    Finset.filter (fun m => _v20 = ProposalMsg.round m) faulty_proposals,
                Finmap.keys s.msgs_prevote = Finset.Icc 0 s.MaxRound,
                ∀ _v22 ∈ Finset.Icc 0 s.MaxRound,
                  Finmap.lookupD _v22 s.msgs_prevote = Finset.filter (fun m => _v22 = VoteMsg.round m) faulty_prevotes,
                Finmap.keys s.msgs_precommit = Finset.Icc 0 s.MaxRound,
                ∀ _v24 ∈ Finset.Icc 0 s.MaxRound,
                  Finmap.lookupD _v24 s.msgs_precommit =
                    Finset.filter (fun m => _v24 = VoteMsg.round m) faulty_precommits,
                s.last_action = "INIT"]]]]

-- Use this action as the initial action to reason about inductive invariants
def ind_init (s : State) : Prop :=
  ws_and [True,
    ∃ (iround : Finmap (fun _ : Int => Int)),
      (Finmap.keys iround = s.Corr ∧ ∀ k0 ∈ s.Corr, Finmap.lookupD k0 iround ∈ Finset.Icc 0 s.MaxRound) ∧
        ws_and [True,
          ∃ (istep : Finmap (fun _ : Int => Step)),
            (Finmap.keys istep = s.Corr ∧
                ∀ k0 ∈ s.Corr,
                  Finmap.lookupD k0 istep ∈
                    insert Step.PROPOSE
                      (insert Step.PREVOTE (insert Step.PRECOMMIT (insert Step.DECIDED (∅ : Finset Step))))) ∧
              ws_and [True,
                ∃ (idecision : Finmap (fun _ : Int => Int)),
                  (Finmap.keys idecision = s.Corr ∧
                      ∀ k0 ∈ s.Corr, Finmap.lookupD k0 idecision ∈ s.ValidValues ∪ insert (-1) (∅ : Finset Int)) ∧
                    ws_and [True,
                      ∃ (ilocked_value : Finmap (fun _ : Int => Int)),
                        (Finmap.keys ilocked_value = s.Corr ∧
                            ∀ k0 ∈ s.Corr,
                              Finmap.lookupD k0 ilocked_value ∈ s.ValidValues ∪ insert (-1) (∅ : Finset Int)) ∧
                          ws_and [True,
                            ∃ (ilocked_round : Finmap (fun _ : Int => Int)),
                              (Finmap.keys ilocked_round = s.Corr ∧
                                  ∀ k0 ∈ s.Corr,
                                    Finmap.lookupD k0 ilocked_round ∈
                                      Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int)) ∧
                                ws_and [True,
                                  ∃ (ivalid_value : Finmap (fun _ : Int => Int)),
                                    (Finmap.keys ivalid_value = s.Corr ∧
                                        ∀ k0 ∈ s.Corr,
                                          Finmap.lookupD k0 ivalid_value ∈
                                            s.ValidValues ∪ insert (-1) (∅ : Finset Int)) ∧
                                      ws_and [True,
                                        ∃ (ivalid_round : Finmap (fun _ : Int => Int)),
                                          (Finmap.keys ivalid_round = s.Corr ∧
                                              ∀ k0 ∈ s.Corr,
                                                Finmap.lookupD k0 ivalid_round ∈
                                                  Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int)) ∧
                                            ws_and [True,
                                              ∃ (imsgs_propose : Finmap (fun _ : Int => Finset ProposalMsg)),
                                                (Finmap.keys imsgs_propose = Finset.Icc 0 s.MaxRound ∧
                                                    ∀ k0 ∈ Finset.Icc 0 s.MaxRound,
                                                      Finmap.lookupD k0 imsgs_propose ⊆
                                                        Finset.image
                                                          (fun _v218 =>
                                                            ProposalMsg.mk (((_v218).2).2).1 ((_v218).2).1 (_v218).1
                                                              (((_v218).2).2).2)
                                                          (Finset.product (s.Corr ∪ s.Faulty)
                                                            (Finset.product (Finset.Icc 0 s.MaxRound)
                                                              (Finset.product
                                                                (s.ValidValues ∪ s.InvalidValues ∪
                                                                  insert (-1) (∅ : Finset Int))
                                                                (Finset.Icc 0 s.MaxRound ∪
                                                                  insert (-1) (∅ : Finset Int)))))) ∧
                                                  ws_and [True,
                                                    ∃ (imsgs_prevote : Finmap (fun _ : Int => Finset VoteMsg)),
                                                      (Finmap.keys imsgs_prevote = Finset.Icc 0 s.MaxRound ∧
                                                          ∀ k0 ∈ Finset.Icc 0 s.MaxRound,
                                                            Finmap.lookupD k0 imsgs_prevote ⊆
                                                              Finset.image
                                                                (fun _v219 =>
                                                                  VoteMsg.mk ((_v219).2).2 VoteKind.PREVOTE
                                                                    ((_v219).2).1 (_v219).1)
                                                                (Finset.product (s.Corr ∪ s.Faulty)
                                                                  (Finset.product (Finset.Icc 0 s.MaxRound)
                                                                    (s.ValidValues ∪ s.InvalidValues ∪
                                                                      insert (-1) (∅ : Finset Int))))) ∧
                                                        ws_and [True,
                                                          ∃ (imsgs_precommit : Finmap (fun _ : Int => Finset VoteMsg)),
                                                            (Finmap.keys imsgs_precommit = Finset.Icc 0 s.MaxRound ∧
                                                                ∀ k0 ∈ Finset.Icc 0 s.MaxRound,
                                                                  Finmap.lookupD k0 imsgs_precommit ⊆
                                                                    Finset.image
                                                                      (fun _v220 =>
                                                                        VoteMsg.mk ((_v220).2).2 VoteKind.PRECOMMIT
                                                                          ((_v220).2).1 (_v220).1)
                                                                      (Finset.product (s.Corr ∪ s.Faulty)
                                                                        (Finset.product (Finset.Icc 0 s.MaxRound)
                                                                          (s.ValidValues ∪ s.InvalidValues ∪
                                                                            insert (-1) (∅ : Finset Int))))) ∧
                                                              ws_and [insert "INIT"
                                                                    (insert "INSERT_PROPOSAL"
                                                                      (insert "UPON_PROPOSAL_PROPOSE"
                                                                        (insert "UPON_PROPOSAL_PROPOSE_AND_PREVOTE"
                                                                          (insert "UPON_QUORUM_PREVOTES_ANY"
                                                                            (insert
                                                                              "UPON_PROPOSAL_PREVOTE_OR_COMMIT_AND_PREVOTE"
                                                                              (insert "UPON_QUORUM_PRECOMMITS_ANY"
                                                                                (insert
                                                                                  "UPON_PROPOSAL_PRECOMMIT_NO_DECISION"
                                                                                  (insert "ON_TIMEOUT_PROPOSE"
                                                                                    (insert "ON_QUORUM_NIL_PREVOTES"
                                                                                      (insert "ON_ROUND_CATCHUP"
                                                                                        (∅ : Finset String))))))))))) ≠
                                                                  (∅ : Finset String),
                                                                ∃
                                                                  iaction ∈
                                                                    insert "INIT"
                                                                      (insert "INSERT_PROPOSAL"
                                                                        (insert "UPON_PROPOSAL_PROPOSE"
                                                                          (insert "UPON_PROPOSAL_PROPOSE_AND_PREVOTE"
                                                                            (insert "UPON_QUORUM_PREVOTES_ANY"
                                                                              (insert
                                                                                "UPON_PROPOSAL_PREVOTE_OR_COMMIT_AND_PREVOTE"
                                                                                (insert "UPON_QUORUM_PRECOMMITS_ANY"
                                                                                  (insert
                                                                                    "UPON_PROPOSAL_PRECOMMIT_NO_DECISION"
                                                                                    (insert "ON_TIMEOUT_PROPOSE"
                                                                                      (insert "ON_QUORUM_NIL_PREVOTES"
                                                                                        (insert "ON_ROUND_CATCHUP"
                                                                                          (∅ : Finset String))))))))))),
                                                                  ws_and [∀ _v221 ∈ Finmap.keys imsgs_propose,
                                                                      ∀ _v222 ∈ Finmap.lookupD _v221 imsgs_propose,
                                                                        _v221 = ProposalMsg.round _v222,
                                                                    ∀ _v223 ∈ Finmap.keys imsgs_prevote,
                                                                      ∀ _v224 ∈ Finmap.lookupD _v223 imsgs_prevote,
                                                                        _v223 = VoteMsg.round _v224,
                                                                    ∀ _v225 ∈ Finmap.keys imsgs_precommit,
                                                                      ∀ _v226 ∈ Finmap.lookupD _v225 imsgs_precommit,
                                                                        _v225 = VoteMsg.round _v226,
                                                                    s.round = iround, s.step = istep,
                                                                    s.decision = idecision,
                                                                    s.locked_value = ilocked_value,
                                                                    s.locked_round = ilocked_round,
                                                                    s.valid_value = ivalid_value,
                                                                    s.valid_round = ivalid_round,
                                                                    s.msgs_propose = imsgs_propose,
                                                                    s.msgs_prevote = imsgs_prevote,
                                                                    s.msgs_precommit = imsgs_precommit,
                                                                    s.last_action = iaction,
                                                                    ws_and [∀ _v227 ∈ s.Corr,
                                                                        ws_and [ws_and [_v227 =
                                                                                Finmap.lookupD
                                                                                  (Finmap.lookupD _v227 iround)
                                                                                  s.Proposer ∨
                                                                              ∀
                                                                                _v228 ∈
                                                                                  Finmap.lookupD
                                                                                    (Finmap.lookupD _v227 iround)
                                                                                    imsgs_propose,
                                                                                _v227 ≠ ProposalMsg.src _v228,
                                                                            Finmap.lookupD _v227 istep = Step.PREVOTE ∨
                                                                              Finmap.lookupD _v227 istep =
                                                                                  Step.PRECOMMIT ∨
                                                                                Finmap.lookupD _v227 istep =
                                                                                    Step.DECIDED ∨
                                                                                  ∀
                                                                                    _v229 ∈
                                                                                      Finmap.lookupD
                                                                                        (Finmap.lookupD _v227 iround)
                                                                                        imsgs_prevote,
                                                                                    _v227 ≠ VoteMsg.src _v229,
                                                                            Finmap.lookupD _v227 istep =
                                                                                Step.PRECOMMIT ∨
                                                                              Finmap.lookupD _v227 istep =
                                                                                  Step.DECIDED ∨
                                                                                ∀
                                                                                  _v230 ∈
                                                                                    Finmap.lookupD
                                                                                      (Finmap.lookupD _v227 iround)
                                                                                      imsgs_precommit,
                                                                                  _v227 ≠ VoteMsg.src _v230],
                                                                          ∀
                                                                            _v232 ∈
                                                                              Finset.filter
                                                                                (fun _v231 =>
                                                                                  _v231 > Finmap.lookupD _v227 iround)
                                                                                (Finset.Icc 0 s.MaxRound),
                                                                            ws_and [∀
                                                                                _v233 ∈
                                                                                  Finmap.lookupD _v232 imsgs_propose,
                                                                                _v227 ≠ ProposalMsg.src _v233,
                                                                              ∀
                                                                                _v234 ∈
                                                                                  Finmap.lookupD _v232 imsgs_prevote,
                                                                                _v227 ≠ VoteMsg.src _v234,
                                                                              ∀
                                                                                _v235 ∈
                                                                                  Finmap.lookupD _v232 imsgs_precommit,
                                                                                _v227 ≠ VoteMsg.src _v235]],
                                                                      ∀ _v236 ∈ s.Corr,
                                                                        Finmap.lookupD _v236 istep = Step.PREVOTE →
                                                                          ∃
                                                                            _v237 ∈
                                                                              Finmap.lookupD
                                                                                (Finmap.lookupD _v236 iround)
                                                                                imsgs_prevote,
                                                                            ws_and [VoteMsg.id _v237 ∈
                                                                                s.ValidValues ∪ s.InvalidValues ∪
                                                                                  insert (-1) (∅ : Finset Int),
                                                                              _v236 = VoteMsg.src _v237],
                                                                      ∀ _v238 ∈ s.Corr,
                                                                        Finmap.lookupD _v238 istep = Step.PRECOMMIT →
                                                                          ∃
                                                                            _v239 ∈
                                                                              Finmap.lookupD
                                                                                (Finmap.lookupD _v238 iround)
                                                                                imsgs_precommit,
                                                                            ws_and [VoteMsg.id _v239 ∈
                                                                                s.ValidValues ∪ s.InvalidValues ∪
                                                                                  insert (-1) (∅ : Finset Int),
                                                                              _v238 = VoteMsg.src _v239],
                                                                      ∀ _v240 ∈ s.Corr,
                                                                        Finmap.lookupD _v240 istep = Step.DECIDED →
                                                                          ∃ _v241 ∈ Finset.Icc 0 s.MaxRound,
                                                                            ∃
                                                                              _v242 ∈
                                                                                Finmap.lookupD _v241 imsgs_propose,
                                                                              ws_and [ProposalMsg.src _v242 =
                                                                                  Finmap.lookupD _v241 s.Proposer,
                                                                                ProposalMsg.proposal _v242 =
                                                                                  Finmap.lookupD _v240 idecision],
                                                                      ∀ _v243 ∈ s.Corr,
                                                                        Finmap.lookupD _v243 istep = Step.DECIDED →
                                                                          ∃ _v244 ∈ Finset.Icc 0 s.MaxRound,
                                                                            Finset.card
                                                                                (Finset.filter
                                                                                  (fun _v246 =>
                                                                                    ∃
                                                                                      _v247 ∈
                                                                                        Finset.filter
                                                                                          (fun _v245 =>
                                                                                            VoteMsg.id _v245 =
                                                                                              Finmap.lookupD _v243
                                                                                                idecision)
                                                                                          (Finmap.lookupD _v244
                                                                                            imsgs_precommit),
                                                                                      _v246 = VoteMsg.src _v247)
                                                                                  (s.Corr ∪ s.Faulty)) ≥
                                                                              2 * s.T + 1,
                                                                      ∀ _v248 ∈ s.Corr,
                                                                        (Finmap.lookupD _v248 istep = Step.DECIDED) =
                                                                          (Finmap.lookupD _v248 idecision ∈
                                                                            s.ValidValues),
                                                                      ∀ _v249 ∈ s.Corr,
                                                                        (Finmap.lookupD _v249 ilocked_round = -1) =
                                                                          (Finmap.lookupD _v249 ilocked_value = -1),
                                                                      ∀ _v250 ∈ s.Corr,
                                                                        (Finmap.lookupD _v250 ivalid_round = -1) =
                                                                          (Finmap.lookupD _v250 ivalid_value = -1),
                                                                      ∀ _v251 ∈ s.Corr,
                                                                        ws_and [Finmap.lookupD _v251 ivalid_round ≤
                                                                            Finmap.lookupD _v251 iround,
                                                                          Finmap.lookupD _v251 ilocked_round ≤
                                                                            Finmap.lookupD _v251 iround],
                                                                      ∀ _v252 ∈ s.Corr,
                                                                        Finmap.lookupD _v252 ivalid_round ≠ -1 →
                                                                          Finset.card
                                                                              (Finset.filter
                                                                                (fun _v254 =>
                                                                                  ∃
                                                                                    _v255 ∈
                                                                                      Finset.filter
                                                                                        (fun _v253 =>
                                                                                          VoteMsg.id _v253 =
                                                                                            Finmap.lookupD _v252
                                                                                              ivalid_value)
                                                                                        (Finmap.lookupD
                                                                                          (Finmap.lookupD _v252
                                                                                            ivalid_round)
                                                                                          imsgs_prevote),
                                                                                    _v254 = VoteMsg.src _v255)
                                                                                (s.Corr ∪ s.Faulty)) ≥
                                                                            2 * s.T + 1,
                                                                      ∀ _v256 ∈ s.Corr,
                                                                        Finmap.lookupD _v256 ilocked_round ≠ -1 →
                                                                          ∃ _v257 ∈ Finset.Icc 0 s.MaxRound,
                                                                            ws_and [_v257 ≤ Finmap.lookupD _v256 iround,
                                                                              ∃
                                                                                _v258 ∈
                                                                                  Finmap.lookupD _v257 imsgs_precommit,
                                                                                ws_and [_v256 = VoteMsg.src _v258,
                                                                                  VoteMsg.id _v258 =
                                                                                    Finmap.lookupD _v256
                                                                                      ilocked_value]],
                                                                      ∀ _v259 ∈ s.Corr,
                                                                        ws_and [Finmap.lookupD _v259 ilocked_round = -1,
                                                                            Finmap.lookupD _v259 ilocked_value = -1,
                                                                            ∀ _v260 ∈ Finset.Icc 0 s.MaxRound,
                                                                              ∀
                                                                                _v261 ∈
                                                                                  Finmap.lookupD _v260 imsgs_precommit,
                                                                                _v259 ≠ VoteMsg.src _v261 ∨
                                                                                  VoteMsg.id _v261 = -1] ∨
                                                                          ws_and [Finmap.lookupD _v259 ilocked_round ≠
                                                                              -1,
                                                                            Finmap.lookupD _v259 ilocked_value ≠ -1,
                                                                            ∀ _v262 ∈ Finset.Icc 0 s.MaxRound,
                                                                              ∀
                                                                                _v263 ∈
                                                                                  Finmap.lookupD _v262 imsgs_precommit,
                                                                                (_v259 ≠ VoteMsg.src _v263 ∨
                                                                                    VoteMsg.round _v263 ≤
                                                                                      Finmap.lookupD _v259
                                                                                        ilocked_round) ∨
                                                                                  VoteMsg.id _v263 = -1,
                                                                            ∃
                                                                              _v264 ∈
                                                                                Finmap.lookupD
                                                                                  (Finmap.lookupD _v259 ilocked_round)
                                                                                  imsgs_precommit,
                                                                              ws_and [_v259 = VoteMsg.src _v264,
                                                                                VoteMsg.id _v264 =
                                                                                  Finmap.lookupD _v259 ilocked_value]],
                                                                      ∀ _v265 ∈ Finset.Icc 0 s.MaxRound,
                                                                        ∀ _v266 ∈ Finmap.lookupD _v265 imsgs_prevote,
                                                                          VoteMsg.src _v266 ∈ s.Faulty ∨
                                                                            VoteMsg.id _v266 = -1 ∨
                                                                              ws_and [VoteMsg.id _v266 ≠ -1,
                                                                                (∃
                                                                                    _v267 ∈
                                                                                      Finmap.lookupD _v265
                                                                                        imsgs_propose,
                                                                                    ws_and [ProposalMsg.src _v267 =
                                                                                        Finmap.lookupD _v265 s.Proposer,
                                                                                      ProposalMsg.proposal _v267 =
                                                                                        VoteMsg.id _v266,
                                                                                      ProposalMsg.valid_round _v267 =
                                                                                        -1]) ∨
                                                                                  ∃
                                                                                    _v269 ∈
                                                                                      Finset.filter
                                                                                        (fun rr => rr < _v265)
                                                                                        (Finset.Icc 0 s.MaxRound),
                                                                                    ws_and [∃
                                                                                        _v270 ∈
                                                                                          Finmap.lookupD _v265
                                                                                            imsgs_propose,
                                                                                        ws_and [ProposalMsg.src _v270 =
                                                                                            Finmap.lookupD _v265
                                                                                              s.Proposer,
                                                                                          ProposalMsg.proposal _v270 =
                                                                                            VoteMsg.id _v266,
                                                                                          _v269 =
                                                                                            ProposalMsg.valid_round
                                                                                              _v270],
                                                                                      Finset.card
                                                                                          (Finset.filter
                                                                                            (fun _v272 =>
                                                                                              ∃
                                                                                                _v273 ∈
                                                                                                  Finset.filter
                                                                                                    (fun _v271 =>
                                                                                                      VoteMsg.id _v271 =
                                                                                                        VoteMsg.id
                                                                                                          _v266)
                                                                                                    (Finmap.lookupD
                                                                                                      _v269
                                                                                                      imsgs_prevote),
                                                                                                _v272 =
                                                                                                  VoteMsg.src _v273)
                                                                                            (s.Corr ∪ s.Faulty)) ≥
                                                                                        2 * s.T + 1]],
                                                                      ∀ _v274 ∈ Finset.Icc 0 s.MaxRound,
                                                                        ∀ _v275 ∈ Finmap.lookupD _v274 imsgs_precommit,
                                                                          VoteMsg.src _v275 ∈ s.Corr →
                                                                            ∃
                                                                              _v276 ∈
                                                                                Finmap.lookupD _v274 imsgs_prevote,
                                                                              VoteMsg.src _v276 = VoteMsg.src _v275,
                                                                      ∀ _v277 ∈ Finset.Icc 0 s.MaxRound,
                                                                        ∀ _v278 ∈ Finmap.lookupD _v277 imsgs_precommit,
                                                                          VoteMsg.src _v278 ∈ s.Corr →
                                                                            ws_and [VoteMsg.id _v278 ∈ s.ValidValues,
                                                                                Finset.card
                                                                                    (Finset.filter
                                                                                      (fun _v280 =>
                                                                                        ∃
                                                                                          _v281 ∈
                                                                                            Finset.filter
                                                                                              (fun _v279 =>
                                                                                                VoteMsg.id _v279 =
                                                                                                  VoteMsg.id _v278)
                                                                                              (Finmap.lookupD _v277
                                                                                                imsgs_prevote),
                                                                                          _v280 = VoteMsg.src _v281)
                                                                                      (s.Corr ∪ s.Faulty)) ≥
                                                                                  2 * s.T + 1] ∨
                                                                              ws_and [VoteMsg.id _v278 = -1,
                                                                                Finset.card
                                                                                    (Finset.filter
                                                                                      (fun _v282 =>
                                                                                        ∃
                                                                                          _v283 ∈
                                                                                            Finmap.lookupD _v277
                                                                                              imsgs_prevote,
                                                                                          _v282 = VoteMsg.src _v283)
                                                                                      (s.Corr ∪ s.Faulty)) ≥
                                                                                  2 * s.T + 1],
                                                                      ∀ _v284 ∈ Finset.Icc 0 s.MaxRound,
                                                                        ws_and [∃ _v285 ∈ s.ValidValues,
                                                                            ∃
                                                                              _v286 ∈
                                                                                Finset.Icc 0 s.MaxRound ∪
                                                                                  insert (-1) (∅ : Finset Int),
                                                                              ∀
                                                                                _v287 ∈
                                                                                  Finmap.lookupD _v284 imsgs_propose,
                                                                                ProposalMsg.src _v287 ∈ s.Faulty ∨
                                                                                  ws_and [ws_and [ProposalMsg.src
                                                                                          _v287 =
                                                                                        Finmap.lookupD _v284 s.Proposer,
                                                                                      _v285 =
                                                                                        ProposalMsg.proposal _v287],
                                                                                    _v286 =
                                                                                      ProposalMsg.valid_round _v287],
                                                                          ∀ _v288 ∈ s.Corr,
                                                                            ∃
                                                                              _v289 ∈
                                                                                s.ValidValues ∪
                                                                                  insert (-1) (∅ : Finset Int),
                                                                              ∀
                                                                                _v290 ∈
                                                                                  Finmap.lookupD _v284 imsgs_prevote,
                                                                                _v288 = VoteMsg.src _v290 →
                                                                                  _v289 = VoteMsg.id _v290,
                                                                          ∀ _v291 ∈ s.Corr,
                                                                            ∃
                                                                              _v292 ∈
                                                                                s.ValidValues ∪
                                                                                  insert (-1) (∅ : Finset Int),
                                                                              ∀
                                                                                _v293 ∈
                                                                                  Finmap.lookupD _v284 imsgs_precommit,
                                                                                _v291 = VoteMsg.src _v293 →
                                                                                  _v292 = VoteMsg.id _v293],
                                                                      ∀ _v294 ∈ Finset.Icc 0 s.MaxRound,
                                                                        ∀ _v295 ∈ s.ValidValues,
                                                                          Finset.card
                                                                                (Finset.filter
                                                                                  (fun _v297 =>
                                                                                    ∃
                                                                                      _v298 ∈
                                                                                        Finset.filter
                                                                                          (fun _v296 =>
                                                                                            _v295 = VoteMsg.id _v296)
                                                                                          (Finmap.lookupD _v294
                                                                                            imsgs_precommit),
                                                                                      _v297 = VoteMsg.src _v298)
                                                                                  (s.Corr ∪ s.Faulty)) <
                                                                              2 * s.T + 1 ∨
                                                                            ∀
                                                                              _v300 ∈
                                                                                Finset.filter
                                                                                  (fun _v299 => _v299 > _v294)
                                                                                  (Finset.Icc 0 s.MaxRound),
                                                                              ∀
                                                                                _v301 ∈
                                                                                  s.ValidValues \
                                                                                    insert _v295 (∅ : Finset Int),
                                                                                Finset.card
                                                                                    (Finset.filter
                                                                                      (fun _v303 =>
                                                                                        ∃
                                                                                          _v304 ∈
                                                                                            Finset.filter
                                                                                              (fun _v302 =>
                                                                                                _v301 =
                                                                                                  VoteMsg.id _v302)
                                                                                              (Finmap.lookupD _v300
                                                                                                imsgs_prevote),
                                                                                          _v303 = VoteMsg.src _v304)
                                                                                      (s.Corr ∪ s.Faulty)) <
                                                                                  2 * s.T + 1,
                                                                      ∀ _v305 ∈ s.Corr,
                                                                        ∀ _v306 ∈ Finset.Icc 0 s.MaxRound,
                                                                          ∀ _v307 ∈ s.ValidValues,
                                                                            ∀ _v308 ∈ Finset.Icc 0 s.MaxRound,
                                                                              ws_and [_v308 > _v306,
                                                                                  ∃
                                                                                    _v309 ∈
                                                                                      Finmap.lookupD _v306
                                                                                        imsgs_precommit,
                                                                                    ws_and [ws_and [_v305 =
                                                                                          VoteMsg.src _v309,
                                                                                        VoteMsg.id _v309 ≠ -1],
                                                                                      _v307 ≠ VoteMsg.id _v309],
                                                                                  ∃
                                                                                    _v310 ∈
                                                                                      Finmap.lookupD _v308
                                                                                        imsgs_prevote,
                                                                                    ws_and [_v305 = VoteMsg.src _v310,
                                                                                      _v307 = VoteMsg.id _v310]] →
                                                                                ∃
                                                                                  _v312 ∈
                                                                                    Finset.filter
                                                                                      (fun _v311 =>
                                                                                        ws_and [_v311 ≥ _v306,
                                                                                          _v311 < _v308])
                                                                                      (Finset.Icc 0 s.MaxRound),
                                                                                  Finset.card
                                                                                      (Finset.filter
                                                                                        (fun _v314 =>
                                                                                          ∃
                                                                                            _v315 ∈
                                                                                              Finset.filter
                                                                                                (fun _v313 =>
                                                                                                  _v307 =
                                                                                                    VoteMsg.id _v313)
                                                                                                (Finmap.lookupD _v312
                                                                                                  imsgs_prevote),
                                                                                            _v314 = VoteMsg.src _v315)
                                                                                        (s.Corr ∪ s.Faulty)) ≥
                                                                                    2 * s.T + 1,
                                                                      ∀ _v316 ∈ Finset.Icc 0 s.MaxRound,
                                                                        ws_and [Finmap.lookupD _v316 s.Proposer ∈
                                                                              s.Corr,
                                                                            ∃
                                                                              _v317 ∈
                                                                                Finmap.lookupD _v316 imsgs_propose,
                                                                              ws_and [ProposalMsg.src _v317 =
                                                                                  Finmap.lookupD _v316 s.Proposer,
                                                                                ProposalMsg.valid_round _v317 = -1]] →
                                                                          ∀
                                                                            _v319 ∈
                                                                              Finset.filter (fun _v318 => _v318 < _v316)
                                                                                (Finset.Icc 0 s.MaxRound),
                                                                            ¬∃
                                                                                _v320 ∈
                                                                                  Finmap.lookupD _v319 imsgs_precommit,
                                                                                ws_and [VoteMsg.src _v320 =
                                                                                    Finmap.lookupD _v316 s.Proposer,
                                                                                  VoteMsg.id _v320 ≠ -1],
                                                                      ∀ _v321 ∈ s.Corr,
                                                                        ∀ _v322 ∈ Finset.Icc 0 s.MaxRound,
                                                                          _v322 > Finmap.lookupD _v321 iround ∨
                                                                            _v322 = 0 ∨
                                                                              Finset.card
                                                                                    (Finset.filter
                                                                                        (fun _v325 =>
                                                                                          ∃
                                                                                            _v326 ∈
                                                                                              Finmap.lookupD _v322
                                                                                                imsgs_prevote,
                                                                                            _v325 = VoteMsg.src _v326)
                                                                                        (s.Corr ∪ s.Faulty) ∪
                                                                                      Finset.filter
                                                                                        (fun _v323 =>
                                                                                          ∃
                                                                                            _v324 ∈
                                                                                              Finmap.lookupD _v322
                                                                                                imsgs_precommit,
                                                                                            _v323 = VoteMsg.src _v324)
                                                                                        (s.Corr ∪ s.Faulty)) ≥
                                                                                  s.T + 1 ∨
                                                                                Finset.card
                                                                                    (Finset.filter
                                                                                      (fun _v327 =>
                                                                                        ∃
                                                                                          _v328 ∈
                                                                                            Finmap.lookupD (_v322 - 1)
                                                                                              imsgs_precommit,
                                                                                          _v327 = VoteMsg.src _v328)
                                                                                      (s.Corr ∪ s.Faulty)) ≥
                                                                                  2 * s.T + 1,
                                                                      ∀ _v332 ∈ Finset.Icc 0 s.MaxRound,
                                                                        _v332 <
                                                                            List.foldl
                                                                              (fun acc x => if x > acc then x else acc)
                                                                              0
                                                                              (Finset.toList
                                                                                (Finset.image
                                                                                  (fun k => Finmap.lookupD k iround)
                                                                                  (Finmap.keys iround))) →
                                                                          Finset.card
                                                                              (Finset.filter
                                                                                (fun _v333 =>
                                                                                  ∃
                                                                                    _v334 ∈
                                                                                      Finmap.lookupD _v332
                                                                                        imsgs_precommit,
                                                                                    _v333 = VoteMsg.src _v334)
                                                                                (s.Corr ∪ s.Faulty)) ≥
                                                                            2 * s.T + 1,
                                                                      ∀ _v335 ∈ s.Corr,
                                                                        Finmap.lookupD _v335 ivalid_round =
                                                                            Finmap.lookupD _v335 iround →
                                                                          Finmap.lookupD _v335 istep = Step.PRECOMMIT ∨
                                                                            Finmap.lookupD _v335 istep = Step.DECIDED,
                                                                      ∀ _v336 ∈ s.Corr,
                                                                        Finmap.lookupD _v336 ilocked_round ≤
                                                                          Finmap.lookupD _v336 ivalid_round,
                                                                      ∀ _v337 ∈ s.Corr,
                                                                        Finmap.lookupD _v337 ivalid_round ≠ -1 →
                                                                          ∃
                                                                            _v338 ∈
                                                                              Finmap.lookupD
                                                                                (Finmap.lookupD _v337 ivalid_round)
                                                                                imsgs_precommit,
                                                                            _v337 = VoteMsg.src _v338,
                                                                      ∀ _v339 ∈ Finset.Icc 0 s.MaxRound,
                                                                        ∀ _v340 ∈ Finmap.lookupD _v339 imsgs_propose,
                                                                          ProposalMsg.src _v340 ∈ s.Corr →
                                                                            _v339 >
                                                                              ProposalMsg.valid_round _v340]]]]]]]]]]]]]

-- Inject arbitrary proposal, prevote, and precommit messages by faulty replicas.
def faulty_step (s s' : State) : Prop :=
  ws_and [Finset.Icc 0 s.MaxRound ≠ (∅ : Finset Int),
    ∃ r ∈ Finset.Icc 0 s.MaxRound,
      ws_and [Finset.powerset s.Faulty ≠ (∅ : Finset (Finset Int)),
        ∃ fps1 ∈ Finset.powerset s.Faulty,
          ws_and [s.ValidValues ∪ s.InvalidValues ≠ (∅ : Finset Int),
            ∃ v1 ∈ s.ValidValues ∪ s.InvalidValues,
              ws_and [Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int) ≠ (∅ : Finset Int),
                ∃ vr1 ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int),
                  s'.msgs_propose =
                    Finmap.insert r
                      (Finmap.lookupD r s.msgs_propose ∪ Finset.image (fun _v56 => ProposalMsg.mk v1 r _v56 vr1) fps1)
                      s.msgs_propose]],
        Finset.powerset s.Faulty ≠ (∅ : Finset (Finset Int)),
        ∃ fps2 ∈ Finset.powerset s.Faulty,
          ws_and [s.ValidValues ∪ s.InvalidValues ≠ (∅ : Finset Int),
            ∃ v2 ∈ s.ValidValues ∪ s.InvalidValues,
              s'.msgs_prevote =
                Finmap.insert r
                  (Finmap.lookupD r s.msgs_prevote ∪
                    Finset.image (fun _v57 => VoteMsg.mk v2 VoteKind.PREVOTE r _v57) fps2)
                  s.msgs_prevote],
        Finset.powerset s.Faulty ≠ (∅ : Finset (Finset Int)),
        ∃ fps3 ∈ Finset.powerset s.Faulty,
          ws_and [s.ValidValues ∪ s.InvalidValues ≠ (∅ : Finset Int),
            ∃ v3 ∈ s.ValidValues ∪ s.InvalidValues,
              s'.msgs_precommit =
                Finmap.insert r
                  (Finmap.lookupD r s.msgs_precommit ∪
                    Finset.image (fun _v58 => VoteMsg.mk v3 VoteKind.PRECOMMIT r _v58) fps3)
                  s.msgs_precommit]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.round = s.round,
    s'.step = s.step, s'.decision = s.decision, s'.locked_value = s.locked_value, s'.locked_round = s.locked_round,
    s'.valid_value = s.valid_value, s'.valid_round = s.valid_round, s'.last_action = s.last_action]

-- 14: if proposer(h_p, round_p) = p then
-- 15:   if validValue_p != nil then
-- 16:     proposal <- validValue_p
-- 17:   else:
-- 18:     proposal <- getValue()
-- 19:   broadcast <PROPOSAL, h_p, round_p, proposal, validRound_p>
-- 20: else:
-- 21:   schedule OnTimeoutPropose(h_p, round_p) ...
def insert_proposal (p : Int) (s s' : State) : Prop :=
  ws_and [let _cache59 := Finmap.lookupD p s.round;
    ws_and [p = Finmap.lookupD _cache59 s.Proposer, Finmap.lookupD p s.step = Step.PROPOSE,
      ∀ _v60 ∈ Finmap.lookupD _cache59 s.msgs_propose, p ≠ ProposalMsg.src _v60, s.ValidValues ≠ (∅ : Finset Int),
      ∃ v ∈ s.ValidValues,
        ws_and [s'.msgs_propose =
            Finmap.insert _cache59
              (Finmap.lookupD _cache59 s.msgs_propose ∪
                insert
                  (ProposalMsg.mk (if Finmap.lookupD p s.valid_value ≠ -1 then Finmap.lookupD p s.valid_value else v)
                    _cache59 p (Finmap.lookupD p s.valid_round))
                  (∅ : Finset ProposalMsg))
              s.msgs_propose,
          s'.last_action = "INSERT_PROPOSAL"]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.round = s.round,
    s'.step = s.step, s'.decision = s.decision, s'.locked_value = s.locked_value, s'.locked_round = s.locked_round,
    s'.valid_value = s.valid_value, s'.valid_round = s.valid_round, s'.msgs_prevote = s.msgs_prevote,
    s'.msgs_precommit = s.msgs_precommit]

-- 44: upon 2f+1 current-round PREVOTE nil messages while step_p = prevote
-- 45:   broadcast PRECOMMIT for nil
-- 46:   step_p <- precommit
def on_quorum_of_nil_prevotes (p : Int) (s s' : State) : Prop :=
  ws_and [let _cache77 := Finmap.lookupD p s.round;
    ws_and [Finmap.lookupD p s.step = Step.PREVOTE,
      let _cache79 := Finset.filter (fun m => VoteMsg.id m = -1) (Finmap.lookupD _cache77 s.msgs_prevote);
      ws_and [Finset.card _cache79 ≥ 2 * s.T + 1,
        s'.msgs_precommit =
          Finmap.insert _cache77
            (Finmap.lookupD _cache77 s.msgs_precommit ∪
              insert (VoteMsg.mk (-1) VoteKind.PRECOMMIT _cache77 p) (∅ : Finset VoteMsg))
            s.msgs_precommit,
        s'.step = Finmap.insert p Step.PRECOMMIT s.step, s'.last_action = "ON_QUORUM_NIL_PREVOTES"]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.round = s.round,
    s'.decision = s.decision, s'.locked_value = s.locked_value, s'.locked_round = s.locked_round,
    s'.valid_value = s.valid_value, s'.valid_round = s.valid_round, s'.msgs_propose = s.msgs_propose,
    s'.msgs_prevote = s.msgs_prevote]

-- 55: upon f+1 messages from a higher round
-- 56:   StartRound(round)
def on_round_catchup (p : Int) (s s' : State) : Prop :=
  ws_and [Finset.Icc 0 s.MaxRound ≠ (∅ : Finset Int),
    ∃ rnd ∈ Finset.Icc 0 s.MaxRound,
      ws_and [Finset.powerset (Finmap.lookupD rnd s.msgs_propose) ≠ (∅ : Finset (Finset ProposalMsg)),
        ∃ ev_propose ∈ Finset.powerset (Finmap.lookupD rnd s.msgs_propose),
          ws_and [Finset.powerset (Finmap.lookupD rnd s.msgs_prevote) ≠ (∅ : Finset (Finset VoteMsg)),
            ∃ ev_prevote ∈ Finset.powerset (Finmap.lookupD rnd s.msgs_prevote),
              ws_and [Finset.powerset (Finmap.lookupD rnd s.msgs_precommit) ≠ (∅ : Finset (Finset VoteMsg)),
                ∃ ev_precommit ∈ Finset.powerset (Finmap.lookupD rnd s.msgs_precommit),
                  ws_and [rnd > Finmap.lookupD p s.round,
                    Finset.card
                        (Finset.filter (fun _v80 => ∃ _v81 ∈ ev_propose, _v80 = ProposalMsg.src _v81)
                              (s.Corr ∪ s.Faulty) ∪
                            Finset.filter (fun _v82 => ∃ _v83 ∈ ev_prevote, _v82 = VoteMsg.src _v83)
                              (s.Corr ∪ s.Faulty) ∪
                          Finset.filter (fun _v84 => ∃ _v85 ∈ ev_precommit, _v84 = VoteMsg.src _v85)
                            (s.Corr ∪ s.Faulty)) ≥
                      s.T + 1,
                    Finmap.lookupD p s.step ≠ Step.DECIDED, s'.round = Finmap.insert p rnd s.round,
                    s'.step = Finmap.insert p Step.PROPOSE s.step, s'.last_action = "ON_ROUND_CATCHUP"]]]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.decision = s.decision,
    s'.locked_value = s.locked_value, s'.locked_round = s.locked_round, s'.valid_value = s.valid_value,
    s'.valid_round = s.valid_round, s'.msgs_propose = s.msgs_propose, s'.msgs_prevote = s.msgs_prevote,
    s'.msgs_precommit = s.msgs_precommit]

-- 57: OnTimeoutPropose(height, round)
-- 58:   if height = h_p and round = round_p and step_p = propose then
-- 59:     broadcast PREVOTE for nil
-- 60:     step_p <- prevote
def on_timeout_propose (p : Int) (s s' : State) : Prop :=
  ws_and [let _cache76 := Finmap.lookupD p s.round;
    ws_and [Finmap.lookupD p s.step = Step.PROPOSE, p ≠ Finmap.lookupD _cache76 s.Proposer,
      s'.msgs_prevote =
        Finmap.insert _cache76
          (Finmap.lookupD _cache76 s.msgs_prevote ∪
            insert (VoteMsg.mk (-1) VoteKind.PREVOTE _cache76 p) (∅ : Finset VoteMsg))
          s.msgs_prevote,
      s'.step = Finmap.insert p Step.PREVOTE s.step, s'.last_action = "ON_TIMEOUT_PROPOSE"],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.round = s.round,
    s'.decision = s.decision, s'.locked_value = s.locked_value, s'.locked_round = s.locked_round,
    s'.valid_value = s.valid_value, s'.valid_round = s.valid_round, s'.msgs_propose = s.msgs_propose,
    s'.msgs_precommit = s.msgs_precommit]

-- 49: upon proposal (v, *) and 2f+1 precommits for v while undecided
-- 50:   if valid(v) then
-- 51:     decision_p[h_p] <- v
-- 52:     h_p <- h_p + 1
-- 53:     reset locks, valid value, valid round, and message log
-- 54:     StartRound(0)
--
-- This one-height model records the decision and moves the process to DECIDED.
def upon_proposal_in_precommit_no_decision (p : Int) (s s' : State) : Prop :=
  ws_and [Finmap.lookupD p s.decision = -1, s.ValidValues ≠ (∅ : Finset Int),
    ∃ v ∈ s.ValidValues,
      ws_and [Finset.Icc 0 s.MaxRound ≠ (∅ : Finset Int),
        ∃ rnd ∈ Finset.Icc 0 s.MaxRound,
          ws_and [Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int) ≠ (∅ : Finset Int),
            ∃ vr ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int),
              let _cache75 := Finset.filter (fun m => v = VoteMsg.id m) (Finmap.lookupD rnd s.msgs_precommit);
              ws_and [ProposalMsg.mk v rnd (Finmap.lookupD rnd s.Proposer) vr ∈ Finmap.lookupD rnd s.msgs_propose,
                Finset.card _cache75 ≥ 2 * s.T + 1, s'.decision = Finmap.insert p v s.decision,
                s'.step = Finmap.insert p Step.DECIDED s.step,
                s'.last_action = "UPON_PROPOSAL_PRECOMMIT_NO_DECISION"]]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.round = s.round,
    s'.locked_value = s.locked_value, s'.locked_round = s.locked_round, s'.valid_value = s.valid_value,
    s'.valid_round = s.valid_round, s'.msgs_propose = s.msgs_propose, s'.msgs_prevote = s.msgs_prevote,
    s'.msgs_precommit = s.msgs_precommit]

-- 36: upon proposal (v, *) and 2f+1 current-round prevotes for v
--     while valid(v) and step_p >= prevote
-- 37:   if step_p = prevote then
-- 38:     lockedValue_p <- v
-- 39:     lockedRound_p <- round_p
-- 40:     broadcast PRECOMMIT for v
-- 41:     step_p <- precommit
-- 42:   validValue_p <- v
-- 43:   validRound_p <- round_p
def upon_proposal_in_prevote_or_commit_and_prevote (p : Int) (s s' : State) : Prop :=
  ws_and [let _cache68 := Finmap.lookupD p s.round;
    ws_and [Finmap.lookupD p s.step = Step.PREVOTE ∨ Finmap.lookupD p s.step = Step.PRECOMMIT,
      s.ValidValues ≠ (∅ : Finset Int),
      ∃ v ∈ s.ValidValues,
        ws_and [Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int) ≠ (∅ : Finset Int),
          ∃ vr ∈ Finset.Icc 0 s.MaxRound ∪ insert (-1) (∅ : Finset Int),
            let _cache70 := Finset.filter (fun m => v = VoteMsg.id m) (Finmap.lookupD _cache68 s.msgs_prevote);
            ws_and [ProposalMsg.mk v _cache68 (Finmap.lookupD _cache68 s.Proposer) vr ∈
                Finmap.lookupD _cache68 s.msgs_propose,
              Finset.card _cache70 ≥ 2 * s.T + 1,
              ws_and [Finmap.lookupD p s.step = Step.PREVOTE, s'.locked_value = Finmap.insert p v s.locked_value,
                  s'.locked_round = Finmap.insert p _cache68 s.locked_round,
                  s'.msgs_precommit =
                    Finmap.insert _cache68
                      (Finmap.lookupD _cache68 s.msgs_precommit ∪
                        insert (VoteMsg.mk v VoteKind.PRECOMMIT _cache68 p) (∅ : Finset VoteMsg))
                      s.msgs_precommit,
                  s'.step = Finmap.insert p Step.PRECOMMIT s.step] ∨
                ws_and [¬Finmap.lookupD p s.step = Step.PREVOTE, s'.locked_value = s.locked_value,
                  s'.locked_round = s.locked_round, s'.msgs_precommit = s.msgs_precommit, s'.step = s.step],
              s'.valid_value = Finmap.insert p v s.valid_value, s'.valid_round = Finmap.insert p _cache68 s.valid_round,
              s'.last_action = "UPON_PROPOSAL_PREVOTE_OR_COMMIT_AND_PREVOTE"]]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.round = s.round,
    s'.decision = s.decision, s'.msgs_propose = s.msgs_propose, s'.msgs_prevote = s.msgs_prevote]

-- 22: upon proposal (v, -1) from proposer while step_p = propose
-- 23:   if valid(v) and (lockedRound_p = -1 or lockedValue_p = v) then
-- 24:     broadcast PREVOTE for v
-- 25:   else
-- 26:     broadcast PREVOTE for nil
-- 27:   step_p <- prevote
def upon_proposal_in_propose (p : Int) (s s' : State) : Prop :=
  ws_and [let _cache61 := Finmap.lookupD p s.round;
    ws_and [Finmap.lookupD p s.step = Step.PROPOSE, s.ValidValues ∪ s.InvalidValues ≠ (∅ : Finset Int),
      ∃ v ∈ s.ValidValues ∪ s.InvalidValues,
        ws_and [ProposalMsg.mk v _cache61 (Finmap.lookupD _cache61 s.Proposer) (-1) ∈
            Finmap.lookupD _cache61 s.msgs_propose,
          s'.msgs_prevote =
            Finmap.insert _cache61
              (Finmap.lookupD _cache61 s.msgs_prevote ∪
                insert
                  (VoteMsg.mk
                    (if
                        ws_and [v ∈ s.ValidValues,
                          Finmap.lookupD p s.locked_round = -1 ∨ Finmap.lookupD p s.locked_value = v] then
                      v
                    else -1)
                    VoteKind.PREVOTE _cache61 p)
                  (∅ : Finset VoteMsg))
              s.msgs_prevote,
          s'.step = Finmap.insert p Step.PREVOTE s.step, s'.last_action = "UPON_PROPOSAL_PROPOSE"]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.round = s.round,
    s'.decision = s.decision, s'.locked_value = s.locked_value, s'.locked_round = s.locked_round,
    s'.valid_value = s.valid_value, s'.valid_round = s.valid_round, s'.msgs_propose = s.msgs_propose,
    s'.msgs_precommit = s.msgs_precommit]

-- 28: upon proposal (v, vr) from proposer and 2f+1 prevotes for v in vr
--     while step_p = propose and 0 <= vr < round_p
-- 29:   if valid(v) and (lockedRound_p <= vr or lockedValue_p = v) then
-- 30:     broadcast PREVOTE for v
-- 31:   else
-- 32:     broadcast PREVOTE for nil
-- 33:   step_p <- prevote
def upon_proposal_in_propose_and_prevote (p : Int) (s s' : State) : Prop :=
  ws_and [let _cache62 := Finmap.lookupD p s.round;
    ws_and [Finmap.lookupD p s.step = Step.PROPOSE, s.ValidValues ∪ s.InvalidValues ≠ (∅ : Finset Int),
      ∃ v ∈ s.ValidValues ∪ s.InvalidValues,
        ws_and [Finset.Icc 0 s.MaxRound ≠ (∅ : Finset Int),
          ∃ vr ∈ Finset.Icc 0 s.MaxRound,
            ws_and [vr ≥ 0, vr < _cache62,
              let _cache64 := Finset.filter (fun m => v = VoteMsg.id m) (Finmap.lookupD vr s.msgs_prevote);
              ws_and [ProposalMsg.mk v _cache62 (Finmap.lookupD _cache62 s.Proposer) vr ∈
                  Finmap.lookupD _cache62 s.msgs_propose,
                Finset.card _cache64 ≥ 2 * s.T + 1,
                s'.msgs_prevote =
                  Finmap.insert _cache62
                    (Finmap.lookupD _cache62 s.msgs_prevote ∪
                      insert
                        (VoteMsg.mk
                          (if
                              ws_and [v ∈ s.ValidValues,
                                Finmap.lookupD p s.locked_round ≤ vr ∨ Finmap.lookupD p s.locked_value = v] then
                            v
                          else -1)
                          VoteKind.PREVOTE _cache62 p)
                        (∅ : Finset VoteMsg))
                    s.msgs_prevote,
                s'.step = Finmap.insert p Step.PREVOTE s.step, s'.last_action = "UPON_PROPOSAL_PROPOSE_AND_PREVOTE"]]]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.round = s.round,
    s'.decision = s.decision, s'.locked_value = s.locked_value, s'.locked_round = s.locked_round,
    s'.valid_value = s.valid_value, s'.valid_round = s.valid_round, s'.msgs_propose = s.msgs_propose,
    s'.msgs_precommit = s.msgs_precommit]

-- 47: upon 2f+1 current-round precommits
-- 48:   schedule OnTimeoutPrecommit(h_p, round_p)
--
-- This safety model does not store timers. The transition represents the
-- timeout firing and immediately advances to the next modeled round.
def upon_quorum_of_precommits_any (p : Int) (s s' : State) : Prop :=
  ws_and [let _cache71 := Finmap.lookupD p s.round;
    ws_and [Finset.powerset (Finmap.lookupD _cache71 s.msgs_precommit) ≠ (∅ : Finset (Finset VoteMsg)),
      ∃ my_evidence ∈ Finset.powerset (Finmap.lookupD _cache71 s.msgs_precommit),
        ws_and [Finset.card
              (Finset.filter (fun _v72 => ∃ _v73 ∈ my_evidence, _v72 = VoteMsg.src _v73) (s.Corr ∪ s.Faulty)) ≥
            2 * s.T + 1,
          _cache71 + 1 ∈ Finset.Icc 0 s.MaxRound, Finmap.lookupD p s.step ≠ Step.DECIDED,
          s'.round = Finmap.insert p (_cache71 + 1) s.round, s'.step = Finmap.insert p Step.PROPOSE s.step,
          s'.last_action = "UPON_QUORUM_PRECOMMITS_ANY"]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.decision = s.decision,
    s'.locked_value = s.locked_value, s'.locked_round = s.locked_round, s'.valid_value = s.valid_value,
    s'.valid_round = s.valid_round, s'.msgs_propose = s.msgs_propose, s'.msgs_prevote = s.msgs_prevote,
    s'.msgs_precommit = s.msgs_precommit]

-- 34: upon 2f+1 current-round prevotes while step_p = prevote
-- 35:   schedule OnTimeoutPrevote(h_p, round_p)
--
-- This safety model does not store timers. The transition represents the
-- timeout firing and immediately takes the nil-precommit path.
def upon_quorum_of_prevotes_any (p : Int) (s s' : State) : Prop :=
  ws_and [let _cache65 := Finmap.lookupD p s.round;
    ws_and [Finmap.lookupD p s.step = Step.PREVOTE,
      Finset.powerset (Finmap.lookupD _cache65 s.msgs_prevote) ≠ (∅ : Finset (Finset VoteMsg)),
      ∃ my_evidence ∈ Finset.powerset (Finmap.lookupD _cache65 s.msgs_prevote),
        ws_and [Finset.card
              (Finset.filter (fun _v66 => ∃ _v67 ∈ my_evidence, _v66 = VoteMsg.src _v67) (s.Corr ∪ s.Faulty)) ≥
            2 * s.T + 1,
          s'.msgs_precommit =
            Finmap.insert _cache65
              (Finmap.lookupD _cache65 s.msgs_precommit ∪
                insert (VoteMsg.mk (-1) VoteKind.PRECOMMIT _cache65 p) (∅ : Finset VoteMsg))
              s.msgs_precommit,
          s'.step = Finmap.insert p Step.PRECOMMIT s.step, s'.last_action = "UPON_QUORUM_PREVOTES_ANY"]],
    s'.Corr = s.Corr, s'.Faulty = s.Faulty, s'.N = s.N, s'.T = s.T, s'.ValidValues = s.ValidValues,
    s'.InvalidValues = s.InvalidValues, s'.MaxRound = s.MaxRound, s'.Proposer = s.Proposer, s'.round = s.round,
    s'.decision = s.decision, s'.locked_value = s.locked_value, s'.locked_round = s.locked_round,
    s'.valid_value = s.valid_value, s'.valid_round = s.valid_round, s'.msgs_propose = s.msgs_propose,
    s'.msgs_prevote = s.msgs_prevote]

-- Choose one correct process and execute one enabled protocol transition.
def correct_step (s s' : State) : Prop :=
  ws_and [s.Corr ≠ (∅ : Finset Int),
    ∃ p ∈ s.Corr,
      insert_proposal p s s' ∨
        upon_proposal_in_propose p s s' ∨
          upon_proposal_in_propose_and_prevote p s s' ∨
            upon_quorum_of_prevotes_any p s s' ∨
              upon_proposal_in_prevote_or_commit_and_prevote p s s' ∨
                upon_quorum_of_precommits_any p s s' ∨
                  upon_proposal_in_precommit_no_decision p s s' ∨
                    on_timeout_propose p s s' ∨ on_quorum_of_nil_prevotes p s s' ∨ on_round_catchup p s s']

-- A system transition: either faulty message injection or a correct step.
def step (s s' : State) : Prop :=
  faulty_step s s' ∨
    ws_and [s.Corr ≠ (∅ : Finset Int),
      ∃ p ∈ s.Corr,
        insert_proposal p s s' ∨
          upon_proposal_in_propose p s s' ∨
            upon_proposal_in_propose_and_prevote p s s' ∨
              upon_quorum_of_prevotes_any p s s' ∨
                upon_proposal_in_prevote_or_commit_and_prevote p s s' ∨
                  upon_quorum_of_precommits_any p s s' ∨
                    upon_proposal_in_precommit_no_decision p s s' ∨
                      on_timeout_propose p s s' ∨ on_quorum_of_nil_prevotes p s s' ∨ on_round_catchup p s s']

def Next (s s' : State) : Prop :=
  step s s'

def IsRun (tr : Nat → State) : Prop :=
  init (tr 0) ∧ ∀ (i : Nat), Next (tr i) (tr (i + 1))

-- Reduced coverage projection over per-process protocol state.
-- TODO (M3+): `min_cov` (kind coverage)

end tendermint_single_indinv
