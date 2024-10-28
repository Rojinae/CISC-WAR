from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood
from nnf import config
import random

# Setting up the SAT solver backend for efficient processing
config.sat_backend = "kissat"
E = Encoding()

# Constants representing the ranks and suits of a standard deck of cards
RANKS = list(range(1, 14))
SUITS = ["hearts", "diamonds", "clubs", "spades"]

@proposition(E)
class Card:
    def __init__(self, rank, suit):
        self.rank = rank
        self.suit = suit
    def __repr__(self):
        return f"{self.rank} of {self.suit}"

@proposition(E)
class Owns:
    def __init__(self, player, card):
        self.player = player
        self.card = card
    def __repr__(self):
        return f"{self.player} owns {self.card}"

@proposition(E)
class Plays:
    def __init__(self, player, card, round_number):
        self.player = player
        self.card = card
        self.round_number = round_number
    def __repr__(self):
        return f"{self.player} plays {self.card} in round {self.round_number}"

@proposition(E)
class Wins:
    def __init__(self, player, round_number):
        self.player = player
        self.round_number = round_number
    def __repr__(self):
        return f"{self.player} wins round {self.round_number}"

@proposition(E)
class HigherRank:
    def __init__(self, card_x, card_y):
        self.card_x = card_x
        self.card_y = card_y
    def __repr__(self):
        return f"Rank of {self.card_x} > Rank of {self.card_y}"

@proposition(E)
class SameRank:
    def __init__(self, card_x, card_y):
        self.card_x = card_x
        self.card_y = card_y
    def __repr__(self):
        return f"Rank of {self.card_x} = Rank of {self.card_y}"

@proposition(E)
class Tie:
    def __init__(self, round_number):
        self.round_number = round_number
    def __repr__(self):
        return f"Tie in round {self.round_number}"

@proposition(E)
class GameWins:
    def __init__(self, player):
        self.player = player
    def __repr__(self):
        return f"{self.player} wins the game"

# Global deck of cards
deck = [Card(rank, suit) for rank in RANKS for suit in SUITS]

def random_deck_distribution():
    """
    Randomly distributes the deck between Player A and Player B.
    """
    cards = deck.copy()
    random.shuffle(cards)
    player_a_cards = cards[:26]
    player_b_cards = cards[26:]

    for card in player_a_cards:
        E.add_constraint(Owns("Player A", card))
    for card in player_b_cards:
        E.add_constraint(Owns("Player B", card))

@constraint(E)
def setup_unique_ownership():
    """
    Ensures each card is owned by exactly one player.
    """
    for card in deck:
        E.add_constraint(Owns("Player A", card) ^ Owns("Player B", card))

@constraint(E)
def setup_rank_comparisons():
    """
    Sets up HigherRank and SameRank propositions for all card pairs.
    """
    for card_x in deck:
        for card_y in deck:
            if card_x.rank > card_y.rank:
                E.add_constraint(HigherRank(card_x, card_y))
            elif card_x.rank == card_y.rank:
                E.add_constraint(SameRank(card_x, card_y))

@constraint(E)
def enforce_game_rules():
    """
    Enforces game rules including single card play per round, ownership checks,
    win/tie conditions, and mutual exclusivity of outcomes.
    """
    for round_number in range(1, 53):
        plays_A = [Plays("Player A", card, round_number) for card in deck]
        plays_B = [Plays("Player B", card, round_number) for card in deck]

        # Ensure each player plays exactly one card per round using XOR
        E.add_constraint(plays_A[0] ^ plays_A[1] ^ ... ^ plays_A[-1])
        E.add_constraint(plays_B[0] ^ plays_B[1] ^ ... ^ plays_B[-1])

        for card_x in deck:
            for card_y in deck:
                # Ensure players only play cards they own
                E.add_constraint(Plays("Player A", card_x, round_number) → Owns("Player A", card_x))
                E.add_constraint(Plays("Player B", card_y, round_number) → Owns("Player B", card_y))

                # Enforce winning conditions
                E.add_constraint(
                    (Plays("Player A", card_x, round_number) ∧ Plays("Player B", card_y, round_number) ∧ HigherRank(card_x, card_y)) →
                    Wins("Player A", round_number)
                )
                E.add_constraint(
                    (Plays("Player B", card_y, round_number) ∧ Plays("Player A", card_x, round_number) ∧ HigherRank(card_y, card_x)) →
                    Wins("Player B", round_number)
                )

                # Enforce tie conditions
                E.add_constraint(
                    (Plays("Player A", card_x, round_number) ∧ Plays("Player B", card_y, round_number) ∧ SameRank(card_x, card_y)) →
                    Tie(round_number)
                )

        # Ensure mutual exclusivity of outcomes
        E.add_constraint(
            Wins("Player A", round_number) ∨ Wins("Player B", round_number) ∨ Tie(round_number)
        )
        E.add_constraint(
            ¬(Wins("Player A", round_number) ∧ Wins("Player B", round_number))
        )
        E.add_constraint(
            ¬(Wins("Player A", round_number) ∧ Tie(round_number))
        )
        E.add_constraint(
            ¬(Wins("Player B", round_number) ∧ Tie(round_number))
        )

    # Prevent a card from being played more than once
    for card in deck:
        E.add_constraint(sum([Plays("Player A", card, r) for r in range(1, 53)]) <= 1)
        E.add_constraint(sum([Plays("Player B", card, r) for r in range(1, 53)]) <= 1)

    # Define overall game winner
    total_wins_a = sum([Wins("Player A", r) for r in range(1, 53)])
    total_wins_b = sum([Wins("Player B", r) for r in range(1, 53)])

    E.add_constraint((total_wins_a > total_wins_b) → GameWins("Player A"))
    E.add_constraint((total_wins_b > total_wins_a) → GameWins("Player B"))

def setup_game():
    random_deck_distribution()  # Random initial deck distribution
    setup_unique_ownership()
    setup_rank_comparisons()
    enforce_game_rules()

def analyze_game():
    """
    Analyzes the game to determine total solutions and likelihoods of outcomes.
    """
    total_ties = sum([likelihood(E, Tie(r)) for r in range(1, 53)])
    total_wins_a = sum([likelihood(E, Wins("Player A", r)) for r in range(1, 53)])
    total_wins_b = sum([likelihood(E, Wins("Player B", r)) for r in range(1, 53)])

    print("Total Solutions:", count_solutions(E))
    print("Likelihood of Player A winning first round:", likelihood(E, Wins("Player A", 1)))
    print("Likelihood of Player B winning first round:", likelihood(E, Wins("Player B", 1)))
    print("Likelihood of a tie in the first round:", likelihood(E, Tie(1)))
    print("Total ties across all rounds:", total_ties)
    print("Total wins by Player A across all rounds:", total_wins_a)
    print("Total wins by Player B across all rounds:", total_wins_b)

if __name__ == "__main__":
    setup_game()
    analyze_game()
