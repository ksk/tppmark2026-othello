# Common rules: 4×4 and 6×6 Othello

[English](README.md) | [日本語](README-ja.md)

Only the side length changes between the two boards.
Squares are numbered by row, starting at the top left. A board is a list in that order.
The initial board has 4 stones in the centre: White at the top left and bottom right, Black at the other two squares. Black moves first.

1. Place a stone on an empty square. In each of the 8 horizontal, vertical and diagonal directions, look from the adjacent square. A nonempty consecutive run of opposing stones is captured if one of your own stones follows immediately.
2. A placement is legal only if it captures in at least one direction. Find all captured stones on the board before the move, then flip them and place the new stone. Directions do not wrap across board edges.
3. Change the turn. A player must pass when they have no legal move and the opponent has one. A player with a legal move cannot pass.
4. The game ends when neither player has a legal move, even if empty squares remain. The player with more stones on the board wins; equal counts give a draw.

## Shared rules and certificate interfaces

| File | Role |
|---|---|
| [common/Rules.v](Rules.v) | Defines the rules once with the side length as a parameter |
| [4x4/Rules.v](../4x4/Rules.v) | Concrete rules and types used by the 4×4 certificate checker |
| [6x6/Rules.v](../6x6/Rules.v) | Concrete rules and types used by the 6×6 certificate checkers |

The certificate checkers use concrete types and list-based rules.
Some definitions repeat the common rules so that the certificates can use those types directly.
The equivalence proofs below relate each implementation to the common definitions.
The performance-oriented board representations are described in [6x6/README.md](../6x6/README.md).

`Dimension.side` supplies the side length. `Pieces` supplies the colour, cell and direction types from each certificate implementation.
[boards/Four.v](../boards/Four.v) and [boards/Six.v](../boards/Six.v) instantiate the common definitions with those types and the appropriate side length.

[proofs/equivalence/](../proofs/equivalence/) proves that legal placements, move lists, pass conditions, terminal boards, stone counts and initial positions agree.
The strategy equivalences connect the certificate results to the common definitions used to state the answers.
These equivalences hold for arbitrary boards.

## What is proved

`forces who goal board turn` says that `who` has a finite strategy reaching a final board satisfying `goal`, **whatever legal moves the opponent chooses**.
The strategy chooses one move on its own turn, handles every legal opposing move, and includes forced passes.

`black_score` is the number of black stones minus the number of white stones.
`exact_score b p z` says that, starting from board `b` with player `p` to move, Black has a strategy guaranteeing a final score of at least `z`, and White has one guaranteeing at most `z`.
We call `z` the game value.
Playing the two strategies against each other gives a terminal position with that score, and the value is unique.

A best move is a legal move that preserves the game value.
`optimal_replay z b p actions` describes a finite list of legal moves and forced passes, starting at board `b` with player `p` to move.
It requires the game value to be `z` at every position, including the last, and the last board to be terminal.

Read the initial positions, problems and proofs for [4×4](../solutions/Othello4x4.v) and [6×6](../solutions/Othello6x6.v).
White can force a win on 4×4. On 6×6, the game value is −4.

## Definitions and supporting proofs

| Definition | Contents | Supporting proofs |
|---|---|---|
| [Rules.v](Rules.v) | Boards, initial position, directions, flips, placements, passes and game end | [RuleFacts.v](proofs/RuleFacts.v) |
| [Specification.v](Specification.v) | Captures and legal placements expressed as relations | [SpecificationFacts.v](proofs/SpecificationFacts.v) proves agreement with the executable rules |
| [Game.v](Game.v) | Finite strategies, score bounds, games and best play | [GameFacts.v](proofs/GameFacts.v) proves that strategies can be played against each other, that an exact score is attained and unique, and that best play reaches that score |

The relational specification deliberately describes captures without calling the executable capture function.
Its purpose is to check what the computation means.
The 6×6 [strategy results](../6x6/Semantics/Optimal.v) and [best-play results](../6x6/Semantics/OptimalReplay.v) use the common theorems instead of repeating their proofs.
