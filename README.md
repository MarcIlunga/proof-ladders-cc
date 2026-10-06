# The proof ladders in Constructive Cryptography

The cryptographic problems of the proof ladders [1, 2, 3, 4], formalized as objects and statements
on the Constructive Cryptography library. The objects are the schemes, the interfaces, the systems
and converters (in the library's DSL), and the games; the statements are substitutions
$X_0 \simeq_\varepsilon X_1$ of systems for the admitted distinguishers, distances $\Delta$, game
equivalences with blind winning bounds, and bounds on the winning probabilities of solvers. Theorems
name their reductions, the papers' calling programs as DSL converters, and are stated over abstract
finite types with losses in their sizes; the notes' statements at `{0,1}^λ` are corollaries named
`…_bits`. The symmetric and asymmetric problems are proved; the security theorems of the protocol
ladder are `sorry`, with a comment naming the route of each.

## Proof style

A proof is a chain of small steps in the algebra of systems and converters (`cc_calc`): each step
is an equality of systems, such as a factorization `R = α • S` or a composition law, or a
substitution of one system for another inside a context, through an assumption or a statistical
bound. A step that needs work is a named lemma whose statement says what changes; the theorem's
proof is the chain. Reductions are the contexts of the substitutions. Equalities of DSL systems
are proved on their fresh-sampling automata (`Common/ProbAutomaton`): each component is described
once as a step on its inside systems, and an equality is a map or a kernel between the states.

## Problems

Most problems are stated in two models. In the DSL model the libraries and reductions are DSL
systems and converters. In the sampled-function model a library is a function sampled once and
answered deterministically, a hop is an equality of sampled functions, a bad event is a game on a
sampled function, and each reduction comes with its action on a function, in the shape of
`cbc-mac-cc`'s `cbc_smul_ofFunction`. Each file relates the two models in a section on sampled
functions; in the PRF cascade the relations are steps of its code-based proof
(`PRFCascade/CodeBased`).

| Ladder | Problem | Source | Module | Style | Sampled functions |
|---|---|---|---|---|---|
| symmetric | PRG length extension | [1, §1] | `Symmetric/PRGLengthExtension` | systems | indexed by query number, many-seed PRG |
| symmetric | PRF cascade, and the bonus $k_1 = k_2$ | [1, §2] | `Symmetric/PRFCascade/` (`Basic`, `CodeBased`, `PureSystems`, `Bonus`) | code-based and pure systems | the notes' hybrids: two PRF swaps on functions, then the birthday lemma through the calling program of the last hybrid; bonus reduction explicit |
| symmetric | birthday lemma | [1, §2] | `Common/Symmetric` | systems | indexed, as a game |
| symmetric | GGM | [1, §3] | `Symmetric/GGM` | systems | hybrids sampled, many-seed PRG, stateless steps |
| symmetric | two-block CBC-MAC | [1, §4] | `Symmetric/CBCMAC` | systems and games | reduction `cbc₂` explicit |
| symmetric | encrypt-then-MAC: IND-CPA and INT-CTXT, and CCA | [2], [1, §5] | `Symmetric/EncryptThenMAC` | systems | — |
| symmetric | random-oracle PRF | [1, §6] | `Symmetric/RandomOraclePRF` | games | libraries as converters on the oracle |
| asymmetric | KEM + DEM, Theorem 1, imperfect correctness, CPA variant | [3] | `Asymmetric/KEMDEM` | systems | — |
| asymmetric | RSA-KEM | [1, §7] | `Asymmetric/RSAKEM` | systems | libraries sampled, `c* = R*^e` |
| asymmetric | RSA self-reduction and RSA-PSS | [1, §8] | `Asymmetric/RSAPSS` | systems | self-reduction, indexed challenges |
| protocol | Basic Hash: authentication, unlinkability, replay | [4, §2.1], [5] | `Protocol/BasicHash` | systems | — |
| protocol | signed Diffie–Hellman, Theorem 1 and Corollary 1 | [4, §2.2], [6] | `Protocol/SignedDH` | systems and games | — |
| protocol | signed Diffie–Hellman with a KEM: correctness | [4, §2.4] | `Protocol/SignedDHKEM` | — | — |
| protocol | simplified NTOR, Theorem 2 and Corollary 2 | [4, §2.5], [6] | `Protocol/NTOR` | systems and games | — |
| protocol | multi-user St-CDH and SUF-CMA from single-user, Lemmas 1–2 | [6, §1] | `Protocol/MultiUser` | games | — |

Games are used where a step is a bad event of a sampled function, the shape of the library's
`PDG.ofSingleFunction` and `PDG.ofFunction`: the collision step of CBC-MAC, the partitioning
step of the random-oracle PRF, the birthday lemma, and the collision bounds of the cascade's
pure-systems statements. There the game statements (equivalence and blind bound) and the
distance they give are both stated. The PRF cascade is proved in two styles, one module each,
beside the objects they share (`PRFCascade/Basic`). Its code-based proof
(`PRFCascade/CodeBased`) replays the notes' hybrids, including the PRF swaps as substitutions
through the calling programs, and takes its collision step as the notes do, by the birthday lemma
through the calling program of the last hybrid. Its pure-systems statements
(`PRFCascade/PureSystems`) are about the random functions alone, with no PRF step and no DSL
component; the cascade with ideal components is the converter of a program written as a function
of its inside exchanges. It is $T_2 \circ T_1$, within $q(q-1)/(2|X|)$ of the uniform random
function, by conditional equivalence with blind winning and, as a second theorem, by the
H-coefficient technique (`Common/HCoefficient`). The bonus $k_1 = k_2$ (`PRFCascade/Bonus`), for
which the notes give no proof, mixes the two styles: a PRF swap through a calling program, then
the pure-systems bound on $T \circ T$. Elsewhere the steps are equalities and
substitutions through converters, or bad events of systems that sample per query, bounded by
identical-until-bad on their automata (`Common/UntilBad`).

Winning games, whose flag `win` an oracle call sets, are games in the library's games layer
(`Interface.Game`, `CompatibleSolverClass`): a real system whose MBO is its flag. SUF-CMA and
strong CDH, single- and multi-user, are such games. The guessing reductions `B` of Lemmas 1–2 of
[6] (`StCDH.B`, `SUFCMA.B`) are stated there: a converter that guesses the attacked index, such
that every solver's winning probability for the multi-user game is at most $q$ times its winning
probability for `B` attached to the single-user game, at the paper's budgets (one challenge or
public key, one solution or forgery). Theorems 1–2 of [6] bound every solver's
key-indistinguishability advantage by its winning probabilities for the reductions `B₁`, `B₂`
attached to the multi-user games, and Corollaries 1–2 follow by composing the reductions with
those of Lemmas 1–2; their proofs are that composition. In the game `IND` of [6], a response is
partnered with every initiator that sent its message to its responder, the partnering of
[6, §2].

Not stated: signed KEM and simplified ACME [4, §2.3, §2.6], which have no computational
definitions in the problem set; the security of signed Diffie–Hellman with a KEM; the
random-oracle variant of KEM + DEM. The implementation ladder (program verification) is out of
scope.

## Shared objects

`ProofLadders/Common` holds the notions the problems share and the library lacks. Each module
names its declarations as upstream candidates with their target library module:

- `Common/Probability`: composite laws;
- `Common/Functional`: converters on sampled functions, restated from `cbc-mac-cc` where it
  proves them, and the per-port typing of bounded programs;
- `Common/LazySampling`: lazy sampling, the lazy random dictionary on a sampled table as the
  sampled function;
- `Common/Programs`: per-label call bounds of programs, per invocation and amortized along a
  run, the converters of a program at per-label inside budgets, and the serial composition of
  programs;
- `Common/ProbAutomaton`: probabilistic automata, equality along simulations, and DSL
  compositions as fresh sampling;
- `Common/Memoryless`: memoryless systems, and programs attached to them, whose equalities are
  equalities of reply laws;
- `Common/UntilBad`: identical until bad, for random systems and for probabilistic automata at
  per-port budgets;
- `Common/HCoefficient`: the H-coefficient bound on the transcript distance of random systems;
- `Common/Substitution`: the hybrid argument for substitutions within error functions;
- `Common/Mixtures`: distinguishing resources sampled once, deciding on average, and pairs
  sampled under two laws;
- `Common/Symmetric`: the PRF, PRG, many-seed PRG, birthday and unforgeable-PRF libraries;
- `Common/Encryption`: correctness, left-or-right CCA, one-time and single-challenge DEM security;
- `Common/AuthenticatedEncryption`: `(ind-cpa, int-ctxt) → ae`, and `ρ^cpa`, `ρ^ctxt`, `ρ^ae` as
  steps;
- `Common/PublicKey`: left-or-right CPA and single-challenge CCA of a PKE and a KEM, and the KEM
  correctness error;
- `Common/RSA`: the RSA libraries, as systems and as sampled functions;
- `Common/KeyExchange`: two-pass key exchange, its correctness and key indistinguishability,
  SUF-CMA and strong CDH, single- and multi-user, as games, and key entropy;
- `Common/Game`: the game of a resource with a winning condition on its transcripts, for the
  library's games layer.

## Modelling choices

Each module doc states the modelling choices of its formalization.

## Checking

The library is a Lake dependency, pinned in `lake-manifest.json`, at present to the commit of its
games layer (`cr18-games`, f8841c3, library PR #4); after the merge, the pin moves to `main`:

```sh
lake build
```

The only warnings are `declaration uses 'sorry'`.

## References

1. The symmetric proof ladder, *Security proofs in the style of The Joy of Cryptography*,
   `proof-ladders/symmetric-ladder`, `Notes/selfcontained.tex`.
2. The symmetric proof ladder, `README.md` and `EtM-IND-CPA+CTXT`.
3. M. Barbosa. *Yet another set of HACS examples*, `proof-ladders/asymmetric-ladder`,
   `asymmetric-problems.pdf`, 2025; and its ProofFrog and EasyCrypt solutions,
   `kemdem/ProofFrog` and `kemdem/EasyCrypt`.
4. The protocol ladder, `proof-ladders/protocol-ladder`, `Notes/main.tex`.
5. The protocol ladder, Basic Hash in EasyCrypt, `basic-hash/EasyCrypt`.
6. D. Riepel and P. Rösler. *Basic definitions, constructions, and proofs for unilateral
   authenticated key exchange*, `proof-ladders/protocol-ladder`, `Notes/computational/main.pdf`,
   2025.
