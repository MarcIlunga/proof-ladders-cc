import ProofLadders.Common.Probability
import ProofLadders.Common.Functional
import ProofLadders.Common.LazySampling
import ProofLadders.Common.Programs
import ProofLadders.Common.ProbAutomaton
import ProofLadders.Common.Memoryless
import ProofLadders.Common.UntilBad
import ProofLadders.Common.HCoefficient
import ProofLadders.Common.Substitution
import ProofLadders.Common.Mixtures
import ProofLadders.Common.Symmetric
import ProofLadders.Common.Encryption
import ProofLadders.Common.AuthenticatedEncryption
import ProofLadders.Common.PublicKey
import ProofLadders.Common.RSA
import ProofLadders.Common.KeyExchange
import ProofLadders.Common.Game
import ProofLadders.Symmetric.PRGLengthExtension
import ProofLadders.Symmetric.PRFCascade.Basic
import ProofLadders.Symmetric.PRFCascade.CodeBased
import ProofLadders.Symmetric.PRFCascade.PureSystems
import ProofLadders.Symmetric.PRFCascade.Bonus
import ProofLadders.Symmetric.GGM
import ProofLadders.Symmetric.CBCMAC
import ProofLadders.Symmetric.EncryptThenMAC
import ProofLadders.Symmetric.RandomOraclePRF
import ProofLadders.Asymmetric.KEMDEM
import ProofLadders.Asymmetric.RSAKEM
import ProofLadders.Asymmetric.RSAPSS
import ProofLadders.Protocol.BasicHash
import ProofLadders.Protocol.SignedDH
import ProofLadders.Protocol.SignedDHKEM
import ProofLadders.Protocol.NTOR
import ProofLadders.Protocol.MultiUser

/-!
# The proof ladders in Constructive Cryptography

The cryptographic problems of the proof ladders [1, 2, 3], as objects and statements: schemes,
interfaces, systems, converters and games, and the security statements, as substitutions
`X₀ ≃[ε] X₁` of systems for the admitted distinguishers, distances `Δ`, and game equivalences
with their blind winning bounds.

Most problems are stated twice. In the DSL model the libraries and reductions are DSL systems and
converters. In the sampled-function model a library is a function sampled once and answered
deterministically, a hop is an equality of sampled functions, a bad event is a game on a
sampled function, and each reduction comes with its action on a function; each file relates the
two models, in a section on sampled functions.

`Common` holds the notions the problems share and the library lacks, each an upstream candidate
naming its target module: composite laws, converters on sampled functions, lazy sampling, programs
at per-label budgets, memoryless systems, the hybrid argument for substitutions, distinguishing
mixtures, PRF and PRG libraries, encryption notions, public-key notions, the RSA assumption,
unilateral authenticated key exchange, and the games of winning conditions.

1. The symmetric ladder [1]: PRG length extension, the PRF cascade, GGM, two-block CBC-MAC,
   encrypt-then-MAC, the random-oracle PRF.
2. The asymmetric ladder [2]: KEM + DEM; from the notes of [1], RSA-KEM and RSA-PSS.
3. The protocol ladder [3]: Basic Hash, signed Diffie–Hellman, signed Diffie–Hellman with a KEM,
   simplified NTOR, and the multi-user assumptions from single-user ones, as games.

## References

1. The symmetric proof ladder, `proof-ladders/symmetric-ladder`.
2. The asymmetric proof ladder, `proof-ladders/asymmetric-ladder`.
3. The protocol ladder, `proof-ladders/protocol-ladder`.
-/
