from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood
from nnf import config

# Setting up the SAT solver backend for efficient processing
config.sat_backend = "kissat"
E = Encoding()

# Constants representing the ranks and suits of a standard deck of cards
RANKS = list(range(1, 14))
SUITS = ["hearts", "diamonds", "clubs", "spades"]

@proposition(E)
class Card:
    """
    Represents a single playing card with a rank and suit.
    """
    def __init__(self, rank, suit):
        self.rank = rank
        self.suit = suit

    def __repr__(self):
        return f"{self.rank} of {self.suit}"

@proposition(E)
class Owns:
    """
    Indicates whether a player owns a specific card.
    """
    def __init__(self, player, card):
        self.player = player
        self.card = card

    def __repr__(self):
        return f"{self.player} owns {self.card}"

@proposition(E)
class Plays:
    """
    Represents a player playing a specific card in a given round.
    """
    def __init__(self, player, card, round_number):
        self.player = player
        self.card = card
        self.round_number = round_number

    def __repr__(self):
        return f"{self.player} plays {self.card} in round {self.round_number}"

@proposition(E)
class Wins:
    """
    Represents a player winning a specific round of the game.
    """
    def __init__(self, player, round_number):
        self.player = player
        self.round_number = round_number

    def __repr__(self):
        return f"{self.player} wins round {self.round_number}"

@proposition(E)
class HigherRank:
    """
    Represents a rank comparison between two cards.
    Indicates that card x has a higher rank than card y.
    """
    def __init__(self, card_x, card_y):
        self.card_x = card_x
        self.card_y = card_y

    def __repr__(self):
        return f"Rank of {self.card_x} > Rank of {self.card_y}"

@proposition(E)
class SameRank:
    """
    Represents a rank comparison between two cards.
    Indicates that card x has the same rank as card y.
    """
    def __init__(self, card_x, card_y):
        self.card_x = card_x
        self.card_y = card_y

    def __repr__(self):
        return f"Rank of {self.card_x} = Rank of {self.card_y}"

@proposition(E)
class Tie:
    """
    Represents a tie in a specific round.
    """
    def __init__(self, round_number):
        self.round_number = round_number

    def __repr__(self):
        return f"Tie in round {self.round_number}"

@constraint(E)
def setup_unique_ownership():
    """
    Ensures that each card in the deck is owned by exactly one player.
    This is done by adding a constraint for each card that it must be owned by either Player A or Player B.
    """
    all_cards = [Card(rank, suit) for rank in RANKS for suit in SUITS]
    for card in all_cards:
        owns_A = Owns("Player A", card)
        owns_B = Owns("Player B", card)
        E.add_constraint(owns_A ^ owns_B)

@constraint(E)
def enforce_game_rules():
    """
    Enforces the game rules including playing one card per round, determining the winner,
    and handling ties based on rank comparisons.
    """
    for round_number in range(1, 53):
        # Ensuring each player plays exactly one card per round
        plays_A = [Plays("Player A", Card(rank, suit), round_number) for rank in RANKS for suit in SUITS]
        plays_B = [Plays("Player B", Card(rank, suit), round_number) for rank in RANKS for suit in SUITS]
        
        E.add_constraint(sum(plays_A) == 1)
        E.add_constraint(sum(plays_B) == 1)

        # Adding rank comparison logic to determine winners and ties
        for rank_x in RANKS:
            for rank_y in RANKS:
                for suit_x in SUITS:
                    for suit_y in SUITS:
                        card_x = Card(rank_x, suit_x)
                        card_y = Card(rank_y, suit_y)
                        if rank_x > rank_y:
                            E.add_constraint(
                                (Plays("Player A", card_x, round_number) ∧ Plays("Player B", card_y, round_number) ∧ HigherRank(card_x, card_y)) →
                                Wins("Player A", round_number)
                            )
                        elif rank_x == rank_y:
                            E.add_constraint(
                                (Plays("Player A", card_x, round_number) ∧ Plays("Player B", card_y, round_number) ∧ SameRank(card_x, card_y)) →
                                Tie(round_number)
                            )

def setup_game():
    """
    Initializes the game by setting up the unique ownership and game rules.
    """
    setup_unique_ownership()
    enforce_game_rules()

def analyze_game():
    """
    Analyzes the game to determine how many solutions exist that satisfy all constraints
    and calculates the likelihood of Player A winning the first round.
    """
    print("Total Solutions:", count_solutions(E))
    print("Likelihood of Player A winning first round:", likelihood(E, Wins("Player A", 1)))

if __name__ == "__main__":
    setup_game()
    analyze_game()
