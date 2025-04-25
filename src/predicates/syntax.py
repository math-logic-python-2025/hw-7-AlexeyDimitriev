# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations
from functools import lru_cache
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from src.logic_utils import (
    frozen,
    memoized_parameterless_method,
)

from src.propositions.syntax import (
    Formula as PropositionalFormula,
)


class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """

    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return (
        ((string[0] >= "0" and string[0] <= "9") or (string[0] >= "a" and string[0] <= "e")) and string.isalnum()
    ) or string == "_"


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= "u" and string[0] <= "z" and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= "f" and string[0] <= "t" and string.isalnum()


@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a function name.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]] = None

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments for the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None and len(arguments) > 0
            self.root = root
            self.arguments = tuple(arguments)

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        if self.arguments is None:
            return self.root
        else:
            ans = self.root + '('
            for ind in range(len(self.arguments)):
                ans = ans + repr(self.arguments[ind]) + ','
            ans = ans[:-1:] + ')'
            return ans

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """

        '''if len(string) == 0:
            return [Term('/'), '']'''

        if ord(string[0]) >= ord('u') and ord(string[0]) <= ord('z'):
            ind = 0
            while ind < len(string) and (ord(string[ind]) >= ord('a') and ord(string[ind]) <= ord('z') or string[ind].isdigit()):
                ind += 1
            return [Term(string[:ind]), string[ind:]]
        elif (ord(string[0]) >= ord('a') and ord(string[0]) <= ord('e')) or string[0].isdigit():
            ind = 0
            while ind < len(string) and (ord(string[ind]) >= ord('a') and ord(string[ind]) <= ord('z') or string[ind].isdigit()):
                ind += 1
            return [Term(string[:ind]), string[ind:]]
        elif string[0] == '_':
            return [Term('_'), string[1:]]
        elif ord(string[0]) >= ord('f') and ord(string[0]) <= ord('t'):
            ind = 0
            while ind < len(string) and (ord(string[ind]) >= ord('a') and ord(string[ind]) <= ord('z') or string[ind].isdigit()):
                ind += 1
            '''if ind >= len(string) or string[ind] != '(':
                return [Term('/'), string]'''
            func = string[:ind]
            ind += 1

            '''if ind >= len(string):
                return [Term('/'), string]'''
            left_str = string[ind:]
            terms = [Term._parse_prefix(left_str)[0]]
            left_str = Term._parse_prefix(left_str)[1]
            '''if len(left_str) == 0:
                return [Term('/'), string]'''

            while len(left_str) != 0:
                if left_str[0] == ')':
                    return (Term(func, terms), left_str[1:])
                '''if left_str[0] != ',':
                    return [Term('/'), string]'''
                left_str = left_str[1:]
                terms.append(Term._parse_prefix(left_str)[0])
                left_str = Term._parse_prefix(left_str)[1]

        '''return [Term('/'), string]'''


    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        return Term._parse_prefix(string)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """

        if is_constant(self.root):
            s = set()
            s.add(self.root)
            return s
        elif is_function(self.root):
            s = set()
            for ind in range (len(self.arguments)):
                s = s.union(self.arguments[ind].constants())
            return s
        return set()

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        if is_variable(self.root):
            s = set()
            s.add(self.root)
            return s
        elif is_function(self.root):
            s = set()
            for ind in range(len(self.arguments)):
                s = s.union(self.arguments[ind].variables())
            return s
        return set()

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        if is_function(self.root):
            s = set()
            s.add((self.root, len(self.arguments)))
            for ind in range(len(self.arguments)):
                s = s.union(self.arguments[ind].functions())
            return s
        return set()

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Term:
        """Substitutes in the current term, each constant name `construct` or
        variable name `construct` that is a key in `substitution_map` with the
        term `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current term are substituted (i.e., those originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from
                `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1


@lru_cache(maxsize=100)  # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == "="


@lru_cache(maxsize=100)  # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= "F" and string[0] <= "T" and string.isalnum()


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == "~"


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return string == "&" or string == "|" or string == "->"


@lru_cache(maxsize=100)  # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == "A" or string == "E"


@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments of the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        statement (`~typing.Optional`\\[`Formula`]): the statement quantified by
            the root, if the root is a quantification.
    """

    root: str
    arguments: Optional[Tuple[Term, ...]] = None
    first: Optional[Formula] = None
    second: Optional[Formula] = None
    variable: Optional[str] = None
    statement: Optional[Formula] = None

    def __init__(
        self,
        root: str,
        arguments_or_first_or_variable: Union[Sequence[Term], Formula, str],
        second_or_statement: Optional[Formula] = None,
    ):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable name and statement.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments for the root, if the
                root is a relation name or the equality relation; the first
                operand for the root, if the root is a unary or binary operator;
                the variable name to be quantified by the root, if the root is a
                quantification.
            second_or_statement: the second operand for the root, if the root is
                a binary operator; the statement to be quantified by the root,
                if the root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert isinstance(arguments_or_first_or_variable, Sequence) and not isinstance(
                arguments_or_first_or_variable, str
            )
            if is_equality(root):
                assert len(arguments_or_first_or_variable) == 2
            assert second_or_statement is None
            self.root, self.arguments = root, tuple(arguments_or_first_or_variable)
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula)
            assert second_or_statement is not None
            self.root, self.first, self.second = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.statement
            assert isinstance(arguments_or_first_or_variable, str) and is_variable(arguments_or_first_or_variable)
            assert second_or_statement is not None
            self.root, self.variable, self.statement = (
                root,
                arguments_or_first_or_variable,
                second_or_statement,
            )

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        if self.root == '=':
            return repr(self.arguments[0]) + '=' + repr(self.arguments[1])
        elif self.arguments is not None:
            ans = self.root + '('
            if len(self.arguments) == 0:
                return ans + ')'
            for ind in range(len(self.arguments)):
                ans = ans + str(self.arguments[ind]) + ','
            ans = ans[:-1:] + ')'
            return ans
        elif self.root == '~':
            return '~' + repr(self.first)
        elif self.second is not None:
            return '(' + repr(self.first) + self.root + repr(self.second) + ')'
        else:
            return self.root + self.variable + '[' + repr(self.statement) + ']'



    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'f(y)=c12'``) or by a variable
            name (e.g., ``'f(y)=x12'``), then the parsed prefix will include
            that entire name (and not just a part of it, such as ``'f(y)=x1'``).
        """

        if ord(string[0]) >= ord('F') and ord(string[0]) <= ord('T'):
            func = string[0]
            left_string = string[1:]
            while len(left_string) != 0 and (ord(left_string[0]) >= ord('a') and ord(left_string[0]) <= ord('z') or ord(left_string[0]) >= ord('A') and ord(left_string[0]) <= ord('Z') or left_string[0].isdigit()):
                func = func + left_string[0]
                left_string = left_string[1:]
            left_string = left_string[1:]
            if left_string[0] == ')':
                return [Formula(func, []), left_string[1:]]
            terms = [Term._parse_prefix(left_string)[0]]
            left_string = Term._parse_prefix(left_string)[1]
            while len(left_string) != 0:
                if left_string[0] == ')':
                    return (Formula(func, terms), left_string[1:])
                left_string = left_string[1:]
                terms.append(Term._parse_prefix(left_string)[0])
                left_string = Term._parse_prefix(left_string)[1]
        elif string[0] == '~':
            form = Formula._parse_prefix(string[1:])[0]
            left_string = Formula._parse_prefix(string[1:])[1]
            return [Formula('~', form), left_string]
        elif string[0] == '(':
            left_string = string[1:]
            form1 = Formula._parse_prefix(left_string)[0]
            left_string = Formula._parse_prefix(left_string)[1]
            oper = left_string[0]
            if left_string[0] == '-':
                oper = oper + left_string[1]
                left_string = left_string[2:]
            else:
                left_string = left_string[1:]
            form2 = Formula._parse_prefix(left_string)[0]
            left_string = Formula._parse_prefix(left_string)[1][1:]
            return [Formula(oper, form1, form2), left_string]
        elif string[0] == 'A' or string[0] == 'E':
            quan = string[0]
            left_string = string[1:]
            var = left_string[0]
            left_string = left_string[1:]
            while len(left_string[0]) > 0 and (ord(left_string[0]) >= ord('a') and ord(left_string[0]) <= ord('z') or ord(left_string[0]) >= ord('A') and ord(left_string[0]) <= ord('Z') or left_string[0].isdigit()):
                var = var + left_string[0]
                left_string = left_string[1:]
            left_string = left_string[1:]
            func = Formula._parse_prefix((left_string))[0]
            left_string = Formula._parse_prefix((left_string))[1][1:]
            return [Formula(quan, var, func), left_string]
        elif len(Term._parse_prefix(string)[1]) != len(string):
            term1 = Term._parse_prefix(string)[0]
            left_string = Term._parse_prefix(string)[1]
            left_string[0] == '='
            left_string = left_string[1:]
            term2 = Term._parse_prefix(left_string)[0]
            left_string = Term._parse_prefix(left_string)[1]
            return [Formula('=', [term1, term2]), left_string]




    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        return Formula._parse_prefix(string)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """

        if is_equality(self.root):
            s = set()
            s = s.union(self.arguments[0].constants())
            s = s.union(self.arguments[1].constants())
            return s
        elif is_relation(self.root):
            s = set()
            for ind in range(len(self.arguments)):
                s = s.union(self.arguments[ind].constants())
            return s
        elif is_unary(self.root):
            s = set()
            s = s.union(self.first.constants())
            return s
        elif is_binary(self.root):
            s = set()
            s = s.union(self.first.constants())
            s = s.union(self.second.constants())
            return s
        elif is_quantifier(self.root):
            s = set()
            s = s.union(self.statement.constants())
            return s
        return set()

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """

        if is_equality(self.root):
            s = set()
            s = s.union(self.arguments[0].variables())
            s = s.union(self.arguments[1].variables())
            return s
        elif is_relation(self.root):
            s = set()
            for ind in range(len(self.arguments)):
                s = s.union(self.arguments[ind].variables())
            return s
        elif is_unary(self.root):
            s = set()
            s = s.union(self.first.variables())
            return s
        elif is_binary(self.root):
            s = set()
            s = s.union(self.first.variables())
            s = s.union(self.second.variables())
            return s
        elif is_quantifier(self.root):
            s = set()
            s.add(self.variable)
            s = s.union(self.statement.variables())
            return s
        return set()

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of every variable name that is used in the current formula not
            only within a scope of a quantification on that variable name.
        """

        if is_equality(self.root):
            s = set()
            s = s.union(self.arguments[0].variables())
            s = s.union(self.arguments[1].variables())
            return s
        elif is_relation(self.root):
            s = set()
            for ind in range(len(self.arguments)):
                s = s.union(self.arguments[ind].variables())
            return s
        elif is_unary(self.root):
            s = set()
            s = s.union(self.first.free_variables())
            return s
        elif is_binary(self.root):
            s = set()
            s = s.union(self.first.free_variables())
            s = s.union(self.second.free_variables())
            return s
        elif is_quantifier(self.root):
            s = set()
            s = s.union(self.statement.free_variables())
            if self.variable in s:
                s.remove(self.variable)
            return s
        return set()

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """

        if is_equality(self.root):
            s = set()
            s = s.union(self.arguments[0].functions())
            s = s.union(self.arguments[1].functions())
            return s
        elif is_relation(self.root):
            s = set()
            for ind in range(len(self.arguments)):
                s = s.union(self.arguments[ind].functions())
            return s
        elif is_unary(self.root):
            s = set()
            s = s.union(self.first.functions())
            return s
        elif is_binary(self.root):
            s = set()
            s = s.union(self.first.functions())
            s = s.union(self.second.functions())
            return s
        elif is_quantifier(self.root):
            s = set()
            s = s.union(self.statement.functions())
            return s
        elif is_function(self.root):
            s = set()
            s = s.add((self.root, len(self.arguments)))
            for ind in range(len(self.arguments)):
                s = s.union(self.arguments[ind].functions())
            return s
        return set()

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """

        if is_relation(self.root):
            s = set()
            s.add((self.root, len(self.arguments)))
            return s
        elif is_unary(self.root):
            s = set()
            s = s.union(self.first.relations())
            return s
        elif is_binary(self.root):
            s = set()
            s = s.union(self.first.relations())
            s = s.union(self.second.relations())
            return s
        elif is_quantifier(self.root):
            s = set()
            s = s.union(self.statement.relations())
            return s
        return set()

    def substitute(
        self,
        substitution_map: Mapping[str, Term],
        forbidden_variables: AbstractSet[str] = frozenset(),
    ) -> Formula:
        """Substitutes in the current formula, each constant name `construct` or
        free occurrence of variable name `construct` that is a key in
        `substitution_map` with the term
        `substitution_map`\ ``[``\ `construct`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variable names not allowed in substitution
                terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant name and variable name occurrences originating in the
            current formula are substituted (i.e., those originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable name from `forbidden_variables`
                or a variable name occurrence that becomes bound when that term
                is substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for construct in substitution_map:
            assert is_constant(construct) or is_variable(construct)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

    def propositional_skeleton(
        self,
    ) -> Tuple[PropositionalFormula, Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation name, equality, or quantifier at its
            root with a propositional variable name, consistently such that
            multiple identical such (outermost) subformulas are substituted with
            the same propositional variable name. The propositional variable
            names used for substitution are obtained, from left to right
            (considering their first occurrence), by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a mapping from each propositional
            variable name to the subformula for which it was substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(~Q(y)->x=7))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(~z3->z2)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(~z6->z5)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        # Task 9.8

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula, substitution_map: Mapping[str, Formula]) -> Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each propositional variable name of
                the given propositional skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each propositional variable name with the
            formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(~z3->z2))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))

            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z9&z2)|(~z3->z2))'),
            ...     {'z2': Formula.parse('x=7'), 'z3': Formula.parse('Q(y)'),
            ...      'z9': Formula.parse('Ax[x=7]')})
            ((Ax[x=7]&x=7)|(~Q(y)->x=7))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10
