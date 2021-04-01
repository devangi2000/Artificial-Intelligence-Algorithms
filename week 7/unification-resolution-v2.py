from __future__ import print_function
import sys
import random
from datetime import datetime

__all__ = []
__version__ = 0.1
__date__ = '2017-02-26'
__updated__ = '2017-03-06'

DEBUG = 0
PRINT_TIME = False
RESOURCE_DPLL = 70
RESOURCE_WALKSAT = 49
INPUT_FILE = 'week 7/input_file.txt'
# OUTPUT_FILE = 'output.txt' # OUTPUT_FILE COULD BE 'OUTPUT_FILE = None' for console or file name (e.g. 'OUTPUT_FILE = 'output.txt') for file.'
OUTPUT_FILE = None  # OUTPUT_FILE COULD BE 'OUTPUT_FILE = None' for console or file name (e.g. 'OUTPUT_FILE = 'output.txt') for file.'

PROBABILITY = 0.5
MAX_FLIPS = 1000000
INPUT_SPLITTER = ' '  # the splitter for input data.
VARIABLE_SPLITTER = ','  # the separator for variables guest and table arrangement
AND = '^'
OR = 'v'
NOT = '~'
ALGORITHM = 'DPLL'  # or 'PL_Resolution'


def getInputData(filename):
    #
    # Get data from input file.
    #  Leverage two dimension array data structure to store data for each line.
    _i_guests = 0
    _i_tables = 0
    _i_enemy = 1
    _s_enemy = set()
    _restrictions = []
    _i = 0

    try:
        with open(filename, 'r') as _fp:
            for _each_line in _fp:
                _row = _each_line.strip().split(INPUT_SPLITTER)
                if _i == 0:  # Get no. of guests and tables.
                    _i_guests = int(_row[0])
                    _i_tables = int(_row[1])
                    _i += 1
                else:  # Restrictions
                    _restrictions.append([_row[0], _row[1], _row[2]])
                    if _row[2] == 'E':
                        _s_enemy.add(_row[0])
                        _s_enemy.add(_row[1])
            # Table numbers no need to exceed guests or enemy relation.
            if _i_tables > _i_guests: _i_tables = _i_guests
            # ***New added. Max table numbers should be equal to 1 or the number in the set of enemy group.
            _i_enemy = len(_s_enemy)
            if _i_tables > max(1, _i_enemy): _i_tables = max(1, _i_enemy)

        _fp.close()
        return _i_guests, _i_tables, _restrictions
    except IOError as _err:
        if (DEBUG):
            print('File error: ' + str(_err))
        else:
            pass
        exit()


def setOutputData(filename='', isSatisfy=None, arrangement={}):
    #
    # output results.
    #
    try:
        if filename != None:
            orig_stdout = sys.stdout
            f = file(filename, 'w')
            sys.stdout = f
        else:
            pass
        ##########
        if not isSatisfy:
            print('no')
        else:
            print('yes')
            _sorted_guests = sorted(arrangement)
            for guest in _sorted_guests:
                # print guest and table number.
                print('%s %s' % (guest, arrangement[guest]))
            ###########
        sys.stdout.flush()
        if filename != None:
            sys.stdout = orig_stdout
            f.close()
        else:
            pass
    except IOError as _err:
        if (DEBUG == True):
            print('File error: ' + str(_err))
        else:
            pass
        exit()


class Wedding(object):
    # a class for wedding information & rules generator from input file.
    def __init__(self, guests=0, tables=0, restrictions=0):
        self.guests = guests
        self.tables = tables
        self.restrictions = restrictions
        self.CNFSentance = []
        self.CNFRestriction = []
        self.CNFDomainSpace = []
        self.arrangement = {}

    def execution(self):
        # Main program to enable wedding arrangement.
        #
        _is_satisfiable = False
        _arrangement = {}
        _kb = Prop_KB()
        _plg = Propositional_Logic()

        if self.guests == 0 or self.tables == 0:
            return False, []
        else:
            self.CNFSentance = self.getWeddingRules()
            if DEBUG: print(self.CNFSentance)

        _kb.tell(self.CNFSentance)
        _is_satisfiable = _plg.is_satisfiable(_kb, ALGORITHM)

        if DEBUG: print('_is_satisfiable= %r' % (_is_satisfiable))
        if _is_satisfiable is True or _is_satisfiable is None:  # if satisfiable or run out of time
            if DEBUG: print('_is_satisfiable is True= %r' % (_is_satisfiable))
            _plg.set_timer()
            _arrangement = _plg.WalkSAT(
                _kb.get_sentence())  # Get result model from WalkSAT, or try to get result from WalkSAT
            if _arrangement is not None:
                _is_satisfiable = True  # ***new added but not in the submit version.
                _arrangement = self.getResults(_arrangement)
            elif ALGORITHM == 'DPLL' and _arrangement is None and _is_satisfiable is True:  # if WalkSAT no result but DPLL has a model
                _arrangement = _plg.model  # Get satisfy result model from DPLL if WalkSAT fail.
                _arrangement = self.getResults(_arrangement)
            else:
                _arrangement = {}

            if DEBUG: print('Wedding arrangement=%s, %r' % (_arrangement, (_arrangement is not None)))
        return _is_satisfiable, _arrangement

    def getWeddingRules(self):
        # Every clause is 'OR' connect with each other clause, every sentence is 'AND' connect with each other sentence.
        # atomic = [guest, table]
        # CNF: (AvB) ^ (~C) = [{'A','B'}, {'~C'}]
        # The outer list is a conjunction of clauses. Each inner list is a clause, i.e. a disjunction of literals.

        _everyone_possible_on_any_table = []
        _everyone_only_exist_one_table = []
        _friend_in_same_table = []
        _enemy_in_different_table = []
        _CNFClauses = []
        _tmp_guest = None
        _tmp_set = set()

        # For each guest should be able to assign into any table.
        # v Xai = CNF
        for _guest in range(1, self.guests + 1):
            for _tablei in range(1, self.tables + 1):
                if _tmp_guest != _guest:
                    _tmp_guest = _guest
                    _tmp_set = {str(_guest) + VARIABLE_SPLITTER + str(_tablei)}
                else:
                    _tmp_set.add(str(_guest) + VARIABLE_SPLITTER + str(_tablei))
            _everyone_possible_on_any_table.append(_tmp_set)

        # And everyone should be at only one table
        # CNF
        # ^[~(Xai ^ Xaj)] = ^[(~Xai v ~Xaj)]
        for _guest in range(1, self.guests + 1):
            for _tablei in range(1, self.tables + 1):
                for _tablej in range(1, self.tables + 1):
                    if (_tablei != _tablej):
                        _everyone_only_exist_one_table.append({NOT + str(_guest) + VARIABLE_SPLITTER + str(_tablei),
                                                               NOT + str(_guest) + VARIABLE_SPLITTER + str(_tablej)})

        # for each pair of friends, guest a and b should in same table.
        # ^[(~Xai v Xbi)^(Xai v ~Xbi)] = CNF
        for _rule in self.restrictions:
            if _rule[2] == 'F':
                for _tablei in range(1, self.tables + 1):
                    _friend_in_same_table.append({NOT + str(_rule[0]) + VARIABLE_SPLITTER + str(_tablei),
                                                  str(_rule[1]) + VARIABLE_SPLITTER + str(_tablei)})
                    _friend_in_same_table.append({str(_rule[0]) + VARIABLE_SPLITTER + str(_tablei),
                                                  NOT + str(_rule[1]) + VARIABLE_SPLITTER + str(_tablei)})

                    # for each pair of enemies, guest a and b should not in same table.
            #  ^ [~(Xai ^ Xbi)]=^[~Xai v ~Xbi] = CNF
            elif _rule[2] == 'E':
                for _tablej in range(1, self.tables + 1):
                    _enemy_in_different_table.append({NOT + str(_rule[0]) + VARIABLE_SPLITTER + str(_tablej),
                                                      NOT + str(_rule[1]) + VARIABLE_SPLITTER + str(_tablej)})
                else:
                    pass

        if _everyone_possible_on_any_table != []: _CNFClauses.extend(_everyone_possible_on_any_table)
        if _everyone_only_exist_one_table != []: _CNFClauses.extend(_everyone_only_exist_one_table)
        if _friend_in_same_table != []: _CNFClauses.extend(_friend_in_same_table)
        if _enemy_in_different_table != []: _CNFClauses.extend(_enemy_in_different_table)

        #         if _everyone_only_exist_one_table != []: self.CNFDomainSpace.extend(_everyone_only_exist_one_table)
        #         if _everyone_possible_on_any_table != []: self.CNFDomainSpace.extend(_everyone_possible_on_any_table)
        #
        #         if _friend_in_same_table != []: self.CNFRestriction.extend(_friend_in_same_table)
        #         if _enemy_in_different_table != []: self.CNFRestriction.extend(_enemy_in_different_table)

        return _CNFClauses

    def getResults(self, model):
        # Get a model and refined it to the result of arrangement.
        _is_satisfy = False
        _guest_table = []
        _arrangement = {}

        for _symbol in model:
            if model[_symbol] == True:
                _guest_table = _symbol.split(VARIABLE_SPLITTER)
                _arrangement.update({_guest_table[0]: _guest_table[1]})  # {guest: table}

        return _arrangement


class Propositional_Logic(object):
    def __init__(self):
        self.sentence = []
        self.symbols = set()
        self.model = {}  # The truth results
        self.begin_time = None

    def set_timer(self):
        self.begin_time = datetime.now()

    def is_operator(self, symbol=''):
        _is_true = False
        if self.is_and(symbol) or self.is_or(symbol) or self.is_not(symbol): _is_true = True
        return _is_true

    def is_and(self, symbol=''):
        _is_true = False
        if AND in symbol: _is_true = True
        return _is_true

    def is_or(self, symbol=''):
        _is_true = False
        if OR in symbol: _is_true = True
        return _is_true

    def is_not(self, symbol=''):
        _is_true = False
        if NOT in symbol: _is_true = True
        return _is_true

    def is_include_not(self, clauses=[]):
        _is_true = False
        for _clause in clauses:
            for _symbol in _clause:
                if NOT in _symbol: _is_true = True
        return _is_true

    def get_symbols(self, sentence):
        # input clauses is a CNF clauses
        # get all symbols which include positive and negative symbols from clauses and put into symbol set.
        _symbol_set = set()
        for _clause in sentence:
            for _symbol in _clause:
                _symbol_set.add(_symbol)
        return _symbol_set

    def get_positive_symbols(self, sentence=[]):
        # input clauses is a CNF clauses
        # get symbols from clauses and convert it to positive form before put into symbol set.
        _symbol_set = set()
        _sentence = []
        if type(sentence) == set:  # single clause as sentence
            _sentence.append(sentence)
        else:
            _sentence = sentence

        for _clause in _sentence:
            for _symbol in _clause:
                if (self.is_not(_symbol)): _symbol = _symbol[1:]
                _symbol_set.add(_symbol)
        return _symbol_set

    def is_satisfiable(self, KB, algorithm='DPLL', model={}):
        self.begin_time = datetime.now()
        _is_satisfiable = False
        _sentence = KB.get_sentence()
        self.symbols = self.get_symbols(_sentence)
        if DEBUG: print('self.symbols=%s' % (str(sorted(list(self.symbols)))))

        if algorithm == 'DPLL':
            if PRINT_TIME: print('is_satisfiable=>DPLL.Start=>%s' % (str(datetime.now())))
            _is_satisfiable = self.DPLL(_sentence, self.symbols, model)
            if PRINT_TIME: print('is_satisfiable=>DPLL.Finish=>%s' % (str(datetime.now())))
        elif algorithm == 'PL_Resolution':
            _is_satisfiable = self.PL_Resolution(KB)
        return _is_satisfiable

    def DPLL(self, sentence=[], symbols=set(), model={}):
        _symbols = set(symbols)
        _model = dict(model)
        _is_true = False
        _unknown_clauses = []  # clauses with an unknown truth value
        _return = None
        _p = None
        _v = None
        if PRINT_TIME: print('DPLL. is_true_PL. Start=>%s' % (str(datetime.now())))
        for _clause in sentence:
            _return = self.is_true_PL(_clause, _model)
            if _return is False:
                return False
            elif _return is None:
                _unknown_clauses.append(_clause)
            else:
                pass
        if PRINT_TIME: print('DPLL. is_true_PL. finish=>%s' % (str(datetime.now())))
        if _unknown_clauses == []:
            self.model = model
            if DEBUG: print('model = %s' % (sorted(model.items())))
            return True  # model is one of the answer by DPLL.
        else:
            # if _model is None: _model = {}
            # if _symbols is None: _symbols = set()
            _p, _v = self.get_pure_symbol(_symbols, _unknown_clauses)
            if _p:
                _symbols = self.remove_both_symbol(_symbols, _p)
                _model.update({_p: _v})
                return self.DPLL(_unknown_clauses, _symbols, _model)
            else:
                pass

            _p, _v = self.get_unit_clause(_unknown_clauses, _model)
            if _p:
                _symbols = self.remove_both_symbol(_symbols, _p)
                _model.update({_p: _v})
                return self.DPLL(_unknown_clauses, _symbols, _model)
            else:
                pass

            _symbols, _p, _v = self.pop_symbol(_symbols)
            _true_model = dict(_model)
            _true_model.update({_p: _v})
            _false_model = dict(model)
            _false_model.update({_p: not _v})
            if (datetime.now() - self.begin_time).total_seconds() >= RESOURCE_DPLL:
                return None
            return (self.DPLL(_unknown_clauses, _symbols, _true_model) or self.DPLL(_unknown_clauses, _symbols,
                                                                                    _false_model))

    def get_pure_symbol(self, clause=set(), sentence=[]):
        # DPLL algorithm get pure symbol which only exist positive form in whole sentence (or negative form in whole sentence.)
        _is_not_symbol = ''
        _positive_symbol = ''
        _negative_symbol = ''
        if PRINT_TIME: print('get_pure_symbol=>Start=>%s' % (str(datetime.now())))
        for _symbol in clause:
            _has_positive = False
            _has_negative = False
            _is_not_symbol = False
            for _clause in sentence:
                if self.is_not(_symbol):
                    _negative_symbol = _symbol
                    _positive_symbol = _symbol[
                                       1:]  # If the symbol include a ~ in front of it. It's negative symbol and program will remove ~ from symbol
                    _is_not_symbol = True  # The symbol include a ~ in front of it.
                else:
                    _possibly_sorted = _symbol
                    _negative_symbol = NOT + _symbol

                if _positive_symbol in _clause: _has_positive = True
                if _negative_symbol in _clause: _has_negative = True
            # return negative symbol asap.
            if (_has_positive == False) and (_has_negative == True):  # flip the symbol and value
                return _positive_symbol, False

        if PRINT_TIME: print('get_pure_symbol=>finish=>%s' % (str(datetime.now())))
        if (_has_positive == True) and (_has_negative == False):
            return _positive_symbol, True
        else:
            return None, None

    def get_unit_clause(self, sentence, model):
        # Return one of unit clause in a sentence.
        # a unit clause only contains single literal.
        _literal = ''
        if PRINT_TIME: print('get_unit_clause=>Start=>%s' % (str(datetime.now())))
        for _clause in sentence:
            if len(_clause) == 1:
                _literal = next(iter(_clause))
                if (self.is_not(_literal)):  # Find negative unit clause asap.
                    return _literal[1:], False
                else:
                    pass
        if PRINT_TIME: print('get_unit_clause=>finish=>%s' % (str(datetime.now())))
        if _literal != '':
            return _literal, True
        else:
            return None, None

    def remove_symbol(self, symbols=set(), remove_symbol=''):
        # Remove the symbol from symbol set
        symbols.discard(remove_symbol)
        return symbols

    def remove_both_symbol(self, symbols=set(), remove_symbol=''):
        # Remove a symbol and its negative form from symbol set
        _positive_symbol = ''
        _negative_symbol = ''

        if (self.is_not(remove_symbol)):
            # if symbol include ~ operator
            _positive_symbol = remove_symbol[1:]
            _negative_symbol = remove_symbol
        else:
            _positive_symbol = remove_symbol
            _negative_symbol = NOT + remove_symbol
        symbols.discard(_positive_symbol)
        symbols.discard(_negative_symbol)
        return symbols

    def pop_symbol(self, symbols=set()):
        # Pop a symbol with a boolean=True value from symbol set
        # If the symbol is negative form, then convert it to positive symbol and flip the boolean value to False.
        _symbol = ''
        _bl = True

        if symbols == set():
            return symbols, None
        else:
            for _s in symbols:
                if self.is_not(_s):
                    _symbol = _s
                    symbols.discard(_symbol)
                    break;
            if _symbol == '':
                _symbol = symbols.pop()

        if (self.is_not(_symbol)):
            # if symbol include ~ operator
            _symbol = _symbol[1:]
            _bl = False
            symbols.discard(_symbol)
        else:
            symbols.discard(NOT + _symbol)
        return symbols, _symbol, _bl

    def get_random_symbol(self, clause=set()):
        # Will get a symbol from symbol set with its boolean value=True. The selected symbol will still keep in the symbol set.
        # If the symbol is negative form, convert it to positive form and flip the boolean value = False.
        _symbol = ''
        _bl = True
        if clause == set():
            return None
        else:
            _symbol = random.sample(clause, 1)
            _symbol = _symbol[0]  # get symbol from list
            _bl = True

        if (self.is_not(_symbol)):
            # if symbol include ~ operator
            _symbol = _symbol[1:]
            _bl = False
        return _symbol, _bl

    def is_true_PL(self, clause=set(), model={}):
        _is_true = False
        _is_not_symbol = False
        _symbol = ''
        _value = None

        if model == {}: return None

        for _literal in clause:
            _value = None
            _is_not_symbol = False
            if (self.is_not(_literal)):
                _is_not_symbol = True
                _symbol = _literal[1:]
            else:
                _symbol = _literal

            _value = model.get(_symbol)  # always convert symbol in clause to positive form to compare with model.
            if (_value == True and _is_not_symbol == False) or (_value == False and _is_not_symbol == True):
                # if the value is true and original symbol does not include ~. (or the value is false and original symbol include ~)
                _is_true = True
                break
            elif (_value == False and _is_not_symbol == False) or (_value == True and _is_not_symbol == True):
                pass
            else:  # _value is None
                _is_true = None

        if _is_true:
            return True
        elif _is_true is None:
            return None
        else:
            return False

    def WalkSAT(self, sentence=[], p=PROBABILITY, max_flips=MAX_FLIPS):
        _symbols = self.get_positive_symbols(sentence)
        _model = {}

        # Random assignment true or false to the symbol in symbol set
        _model = {symbol: random.choice([True, False]) for symbol in _symbols}

        for _i in range(max_flips):
            _satisfied_clauses, _unsatisfied_clauses = [], []
            for clause in sentence:
                if self.is_true_PL(clause, _model):
                    _satisfied_clauses.append(clause)
                else:
                    _unsatisfied_clauses.append(clause)
            if _unsatisfied_clauses == []:  # if there is no 'not satisfied' clause in sentence.
                self.model = _model
                return _model
            clause = random.choice(_unsatisfied_clauses)
            if random.random() < p:
                _symbol, _v = self.get_random_symbol(clause)
            else:
                # Flip the symbol in clause that maximizes the number of satisfiable clauses
                _symbol = self.get_max_satisfiable_symbol(clause, sentence, _model)
            _model[_symbol] = not _model[_symbol]
            # If no solution is found within the flip limit, will return None
            if (datetime.now() - self.begin_time).total_seconds() >= RESOURCE_WALKSAT:
                return None
        if DEBUG: print('max_flips=%d' % (max_flips))
        return None

    def get_max_satisfiable_symbol(self, selected_clause, sentence, model):
        # Flip the symbol in clause and get the maximizes number of satisfiable clauses
        _max_symbol = ''
        _max_count = 0
        _symbols = self.get_positive_symbols(selected_clause)
        for _symbol in _symbols:
            _count = 0
            for _clause in sentence:
                if self.is_true_PL(_clause, self.flip_model(model, _symbol)):
                    _count += 1
            if _max_count < _count:
                _max_count = _count
                _max_symbol = _symbol
        return _max_symbol

    def flip_model(self, model, symbol):
        # Flip the symbol in given model
        _model = dict(model)
        _model[symbol] = not _model[symbol]
        return _model

    def PL_Resolution(self, KB=None, alpha=None):
        _clauses = []
        _clause_pairs = []
        _is_satisfiable = False
        #        _is_only_negative_literal = True
        if alpha is None and KB is not None:
            _is_satisfiable = True
            _clauses = KB.get_sentence()
        else:
            _clauses = KB.get_sentence().append({NOT + alpha})  # KB ^ ~alpha

        _new = []

        while True:
            n = len(_clauses)
            for i in range(n):
                for j in range(i + 1, n):
                    _clause_pairs.append((_clauses[i], _clauses[j]))

            for (ci, cj) in _clause_pairs:
                _resolvents = self.PL_Resolve(ci, cj)
                if set() in _resolvents:
                    if DEBUG: print('_resolvents=:%s' % (_resolvents))
                    if _is_satisfiable:
                        if DEBUG: print('resolvent is empty set()')
                        return False
                    else:
                        if DEBUG: print('resolvent is empty set()')
                        return True
                if _resolvents != []:
                    _new = self.add_set(_new, _resolvents)
                    # add resolvents into _new set.
            if self.is_subset_in_list(_new, _clauses):
                if _is_satisfiable:
                    if DEBUG: print('new is set of clauses')
                    return True
                else:
                    if DEBUG: print('new is set of clauses')
                    return False

            for _clause in _new:
                if _clause not in _clauses:
                    _clauses.append(_clause)
            _new = []
            if DEBUG: print('PL_Resolution=>clauses:%s' % (_clauses))

    def PL_Resolve(self, ci, cj):
        # Return all clauses that can be obtained by resolving clauses ci and cj.
        _clauses = []

        for _symbol_i in ci:
            for _symbol_j in cj:
                if (_symbol_i == NOT + _symbol_j) or (_symbol_j == NOT + _symbol_i):
                    _dnew = self.get_unique_set(self.remove_symbol(set(ci), _symbol_i),
                                                self.remove_symbol(set(cj), _symbol_j))
                    _clauses.append(_dnew)

        return _clauses

    def get_unique_set(self, clausei, clausej):
        # Join clause i and j to form a new clause without redundant literal.
        _unique_set = clausei
        for _symbol in clausej:
            _unique_set.add(_symbol)
        return _unique_set

    def add_set(self, set_list, sets):
        # Add sets into list and avoid redundant set
        _set_list = list(set_list)
        for _set in sets:
            _is_exist = False
            for _existing_set in _set_list:
                if _existing_set == _set:
                    _is_exist = True
            if not _is_exist:
                _set_list.append(_set)
        return _set_list

    def is_subset_in_list(self, subsets, set_list):
        # if all set in subsets are included in set list, return True.
        _is_subset = True

        for _subset in subsets:
            if not (_subset in set_list):
                _is_subset = False
                break
        return _is_subset


class Prop_KB(object):

    def __init__(self, clause=None):
        self.agenda = []
        self.sentence = []

        if clause is not None:
            self.tell(clause)

    def tell(self, clause):
        _is_known = False
        if clause in self.sentence:
            _is_known = True
        else:
            self.sentence.extend(clause)
        return _is_known

    def ask(self, qery):
        _isTrue = False
        return _isTrue

    def get_sentence(self):
        return self.sentence


if __name__ == "__main__":

    '''
        Main program.
            Construct wedding class with input data.
            Build CNF sentences and tell to Prop_KB.
            Ask Prop_KB to provide a solution.
            Prop_KB will check the KB isA satisfiable then tell one solution.
    '''
    # program_name = sys.argv[0]
    # input_file = sys.argv[1]
    input_file = INPUT_FILE
    actions = []
    value = 0

    i_guests, i_tables, restrictions = getInputData(input_file)
    if DEBUG: print('guests=%d, tables=%d, restrictions=%s' % (i_guests, i_tables, restrictions))
    w = Wedding(i_guests, i_tables, restrictions)
    isSatisfy, arrangement = w.execution()

    setOutputData(OUTPUT_FILE, isSatisfy, arrangement)