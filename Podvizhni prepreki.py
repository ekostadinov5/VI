import sys
import math
import random
import bisect
from sys import maxsize as infinity
from math import log
from math import exp

"""
Дефинирање на класа за структурата на проблемот кој ќе го решаваме со пребарување.
Класата Problem е апстрактна класа од која правиме наследување за дефинирање на основните 
карактеристики на секој проблем што сакаме да го решиме
"""


class Problem:
    def __init__(self, initial, goal=None):
        self.initial = initial
        self.goal = goal

    def successor(self, state):
        """За дадена состојба, врати речник од парови {акција : состојба}
        достапни од оваа состојба. Ако има многу следбеници, употребете
        итератор кој би ги генерирал следбениците еден по еден, наместо да
        ги генерирате сите одеднаш.

        :param state: дадена состојба
        :return:  речник од парови {акција : состојба} достапни од оваа
                  состојба
        :rtype: dict
        """
        raise NotImplementedError

    def actions(self, state):
        """За дадена состојба state, врати листа од сите акции што може да
        се применат над таа состојба

        :param state: дадена состојба
        :return: листа на акции
        :rtype: list
        """
        return self.successor(state).keys()

    def result(self, state, action):
        """За дадена состојба state и акција action, врати ја состојбата
        што се добива со примена на акцијата над состојбата

        :param state: дадена состојба
        :param action: дадена акција
        :return: резултантна состојба
        """
        possible = self.successor(state)
        return possible[action]

    def goal_test(self, state):
        """Врати True ако state е целна состојба. Даденава имплементација
        на методот директно ја споредува state со self.goal, како што е
        специфицирана во конструкторот. Имплементирајте го овој метод ако
        проверката со една целна состојба self.goal не е доволна.

        :param state: дадена состојба
        :return: дали дадената состојба е целна состојба
        :rtype: bool
        """
        return state == self.goal

    def path_cost(self, c, state1, action, state2):
        """Врати ја цената на решавачкиот пат кој пристигнува во состојбата
        state2 од состојбата state1 преку акцијата action, претпоставувајќи
        дека цената на патот до состојбата state1 е c. Ако проблемот е таков
        што патот не е важен, оваа функција ќе ја разгледува само состојбата
        state2. Ако патот е важен, ќе ја разгледува цената c и можеби и
        state1 и action. Даденава имплементација му доделува цена 1 на секој
        чекор од патот.

        :param c: цена на патот до состојбата state1
        :param state1: дадена моментална состојба
        :param action: акција која треба да се изврши
        :param state2: состојба во која треба да се стигне
        :return: цена на патот по извршување на акцијата
        :rtype: float
        """
        return c + 1

    def value(self):
        """За проблеми на оптимизација, секоја состојба си има вредност. 
        Hill-climbing и сличните алгоритми се обидуваат да ја максимизираат
        оваа вредност.

        :return: вредност на состојба
        :rtype: float
        """
        raise NotImplementedError


"""
Дефинирање на класата за структурата на јазел од пребарување.
Класата Node не се наследува
"""


class Node:
    def __init__(self, state, parent=None, action=None, path_cost=0):
        """Креирај јазол од пребарувачкото дрво, добиен од parent со примена
        на акцијата action

        :param state: моментална состојба (current state)
        :param parent: родителска состојба (parent state)
        :param action: акција (action)
        :param path_cost: цена на патот (path cost)
        """
        self.state = state
        self.parent = parent
        self.action = action
        self.path_cost = path_cost
        self.depth = 0  # search depth
        if parent:
            self.depth = parent.depth + 1

    def __repr__(self):
        return "<Node %s>" % (self.state,)

    def __lt__(self, node):
        return self.state < node.state

    def expand(self, problem):
        """Излистај ги јазлите достапни во еден чекор од овој јазол.

        :param problem: даден проблем
        :return: листа на достапни јазли во еден чекор
        :rtype: list(Node)
        """

        return [self.child_node(problem, action)
                for action in problem.actions(self.state)]

    def child_node(self, problem, action):
        """Дете јазел

        :param problem: даден проблем
        :param action: дадена акција
        :return: достапен јазел според дадената акција
        :rtype: Node
        """
        next_state = problem.result(self.state, action)
        return Node(next_state, self, action,
                    problem.path_cost(self.path_cost, self.state,
                                      action, next_state))

    def solution(self):
        """Врати ја секвенцата од акции за да се стигне од коренот до овој јазол.

        :return: секвенцата од акции
        :rtype: list
        """
        return [node.action for node in self.path()[1:]]

    def solve(self):
        """Врати ја секвенцата од состојби за да се стигне од коренот до овој јазол.

        :return: листа од состојби
        :rtype: list
        """
        return [node.state for node in self.path()[0:]]

    def path(self):
        """Врати ја листата од јазли што го формираат патот од коренот до овој јазол.

        :return: листа од јазли од патот
        :rtype: list(Node)
        """
        x, result = self, []
        while x:
            result.append(x)
            x = x.parent
        result.reverse()
        return result

    """Сакаме редицата од јазли кај breadth_first_search или 
    astar_search да не содржи состојби - дупликати, па јазлите што
    содржат иста состојба ги третираме како исти. [Проблем: ова може
    да не биде пожелно во други ситуации.]"""

    def __eq__(self, other):
        return isinstance(other, Node) and self.state == other.state

    def __hash__(self):
        return hash(self.state)


"""
Дефинирање на помошни структури за чување на листата на генерирани, но непроверени јазли
"""


class Queue:
    """Queue е апстрактна класа / интерфејс. Постојат 3 типа:
        Stack(): Last In First Out Queue (стек).
        FIFOQueue(): First In First Out Queue (редица).
        PriorityQueue(order, f): Queue во сортиран редослед (подразбирливо,од најмалиот кон
                                 најголемиот јазол).
    """

    def __init__(self):
        raise NotImplementedError

    def append(self, item):
        """Додади го елементот item во редицата

        :param item: даден елемент
        :return: None
        """
        raise NotImplementedError

    def extend(self, items):
        """Додади ги елементите items во редицата

        :param items: дадени елементи
        :return: None
        """
        raise NotImplementedError

    def pop(self):
        """Врати го првиот елемент од редицата

        :return: прв елемент
        """
        raise NotImplementedError

    def __len__(self):
        """Врати го бројот на елементи во редицата

        :return: број на елементи во редицата
        :rtype: int
        """
        raise NotImplementedError

    def __contains__(self, item):
        """Проверка дали редицата го содржи елементот item

        :param item: даден елемент
        :return: дали queue го содржи item
        :rtype: bool
        """
        raise NotImplementedError


class Stack(Queue):
    """Last-In-First-Out Queue."""

    def __init__(self):
        self.data = []

    def append(self, item):
        self.data.append(item)

    def extend(self, items):
        self.data.extend(items)

    def pop(self):
        return self.data.pop()

    def __len__(self):
        return len(self.data)

    def __contains__(self, item):
        return item in self.data


class FIFOQueue(Queue):
    """First-In-First-Out Queue."""

    def __init__(self):
        self.data = []

    def append(self, item):
        self.data.append(item)

    def extend(self, items):
        self.data.extend(items)

    def pop(self):
        return self.data.pop(0)

    def __len__(self):
        return len(self.data)

    def __contains__(self, item):
        return item in self.data


class PriorityQueue(Queue):
    """Редица во која прво се враќа минималниот (или максималниот) елемент
    (како што е определено со f и order). Оваа структура се користи кај
    информирано пребарување"""
    """"""

    def __init__(self, order=min, f=lambda x: x):
        """
        :param order: функција за подредување, ако order е min, се враќа елементот
                      со минимална f(x); ако order е max, тогаш се враќа елементот
                      со максимална f(x).
        :param f: функција f(x)
        """
        assert order in [min, max]
        self.data = []
        self.order = order
        self.f = f

    def append(self, item):
        bisect.insort_right(self.data, (self.f(item), item))

    def extend(self, items):
        for item in items:
            bisect.insort_right(self.data, (self.f(item), item))

    def pop(self):
        if self.order == min:
            return self.data.pop(0)[1]
        return self.data.pop()[1]

    def __len__(self):
        return len(self.data)

    def __contains__(self, item):
        return any(item == pair[1] for pair in self.data)

    def __getitem__(self, key):
        for _, item in self.data:
            if item == key:
                return item

    def __delitem__(self, key):
        for i, (value, item) in enumerate(self.data):
            if item == key:
                self.data.pop(i)


"""
Неинформирано пребарување во рамки на дрво.
Во рамки на дрвото не разрешуваме јамки.
"""


def tree_search(problem, fringe):
    """ Пребарувај низ следбениците на даден проблем за да најдеш цел.

    :param problem: даден проблем
    :param fringe:  празна редица (queue)
    :return: Node
    """
    fringe.append(Node(problem.initial))
    while fringe:
        node = fringe.pop()
        #print(node.state)
        if problem.goal_test(node.state):
            return node
        fringe.extend(node.expand(problem))
    return None


def breadth_first_tree_search(problem):
    """Експандирај го прво најплиткиот јазол во пребарувачкото дрво.

    :param problem: даден проблем
    :return: Node
    """
    return tree_search(problem, FIFOQueue())


def depth_first_tree_search(problem):
    """Експандирај го прво најдлабокиот јазол во пребарувачкото дрво.

    :param problem:даден проблем
    :return: Node
    """
    return tree_search(problem, Stack())


"""
Неинформирано пребарување во рамки на граф
Основната разлика е во тоа што овде не дозволуваме јамки, 
т.е. повторување на состојби
"""


def graph_search(problem, fringe):
    """Пребарувај низ следбениците на даден проблем за да најдеш цел.
     Ако до дадена состојба стигнат два пата, употреби го најдобриот пат.

    :param problem: даден проблем
    :param fringe: празна редица (queue)
    :return: Node
    """
    closed = set()
    fringe.append(Node(problem.initial))
    while fringe:
        node = fringe.pop()
        if problem.goal_test(node.state):
            return node
        if node.state not in closed:
            closed.add(node.state)
            fringe.extend(node.expand(problem))
    return None


def breadth_first_graph_search(problem):
    """Експандирај го прво најплиткиот јазол во пребарувачкиот граф.

    :param problem: даден проблем
    :return: Node
    """
    return graph_search(problem, FIFOQueue())


def depth_first_graph_search(problem):
    """Експандирај го прво најдлабокиот јазол во пребарувачкиот граф.

    :param problem: даден проблем
    :return: Node
    """
    return graph_search(problem, Stack())


def depth_limited_search(problem, limit=50):
    def recursive_dls(node, problem, limit):
        """Помошна функција за depth limited"""
        cutoff_occurred = False
        if problem.goal_test(node.state):
            return node
        elif node.depth == limit:
            return 'cutoff'
        else:
            for successor in node.expand(problem):
                result = recursive_dls(successor, problem, limit)
                if result == 'cutoff':
                    cutoff_occurred = True
                elif result is not None:
                    return result
        if cutoff_occurred:
            return 'cutoff'
        return None

    return recursive_dls(Node(problem.initial), problem, limit)


def iterative_deepening_search(problem):
    for depth in range(sys.maxsize):
        result = depth_limited_search(problem, depth)
        if result is not 'cutoff':
            return result


def uniform_cost_search(problem):
    """Експандирај го прво јазолот со најниска цена во пребарувачкиот граф."""
    return graph_search(problem, PriorityQueue(min, lambda a: a.path_cost))


"""
Информирано пребарување во рамки на граф
"""


def memoize(fn, slot=None):
    """ Запамети ја пресметаната вредност за која била листа од
    аргументи. Ако е специфициран slot, зачувај го резултатот во
    тој slot на првиот аргумент. Ако slot е None, зачувај ги
    резултатите во речник.

    :param fn: зададена функција
    :param slot: име на атрибут во кој се чуваат резултатите од функцијата
    :return: функција со модификација за зачувување на резултатите
    """
    if slot:
        def memoized_fn(obj, *args):
            if hasattr(obj, slot):
                return getattr(obj, slot)
            else:
                val = fn(obj, *args)
                setattr(obj, slot, val)
                return val
    else:
        def memoized_fn(*args):
            if args not in memoized_fn.cache:
                memoized_fn.cache[args] = fn(*args)
            return memoized_fn.cache[args]

        memoized_fn.cache = {}
    return memoized_fn


def best_first_graph_search(problem, f):
    """Пребарувај низ следбениците на даден проблем за да најдеш цел. Користи
     функција за евалуација за да се одлучи кој е сосед најмногу ветува и
     потоа да се истражи. Ако до дадена состојба стигнат два пата, употреби
     го најдобриот пат.

    :param problem: даден проблем
    :param f: дадена функција за евристика
    :return: Node or None
    """
    f = memoize(f, 'f')
    node = Node(problem.initial)
    if problem.goal_test(node.state):
        return node
    frontier = PriorityQueue(min, f)
    frontier.append(node)
    explored = set()
    while frontier:
        node = frontier.pop()
        if problem.goal_test(node.state):
            return node
        explored.add(node.state)
        for child in node.expand(problem):
            if child.state not in explored and child not in frontier:
                frontier.append(child)
            elif child in frontier:
                incumbent = frontier[child]
                if f(child) < f(incumbent):
                    del frontier[incumbent]
                    frontier.append(child)
    return None


def greedy_best_first_graph_search(problem, h=None):
    """ Greedy best-first пребарување се остварува ако се специфицира дека f(n) = h(n).

    :param problem: даден проблем
    :param h: дадена функција за евристика
    :return: Node or None
    """
    h = memoize(h or problem.h, 'h')
    return best_first_graph_search(problem, h)


def astar_search(problem, h=None):
    """ A* пребарување е best-first graph пребарување каде f(n) = g(n) + h(n).

    :param problem: даден проблем
    :param h: дадена функција за евристика
    :return: Node or None
    """
    h = memoize(h or problem.h, 'h')
    return best_first_graph_search(problem, lambda n: n.path_cost + h(n))


def recursive_best_first_search(problem, h=None):
    """Recursive best first search - ја ограничува рекурзијата
    преку следење на f-вредноста на најдобриот алтернативен пат
    од било кој јазел предок (еден чекор гледање нанапред).

    :param problem: даден проблем
    :param h: дадена функција за евристика
    :return: Node or None
    """
    h = memoize(h or problem.h, 'h')

    def RBFS(problem, node, flimit):
        if problem.goal_test(node.state):
            return node, 0  # (втората вредност е неважна)
        successors = node.expand(problem)
        if len(successors) == 0:
            return None, infinity
        for s in successors:
            s.f = max(s.path_cost + h(s), node.f)
        while True:
            # Подреди ги според најниската f вредност
            successors.sort(key=lambda x: x.f)
            best = successors[0]
            if best.f > flimit:
                return None, best.f
            if len(successors) > 1:
                alternative = successors[1].f
            else:
                alternative = infinity
            result, best.f = RBFS(problem, best, min(flimit, alternative))
            if result is not None:
                return result, best.f

    node = Node(problem.initial)
    node.f = h(node)
    result, bestf = RBFS(problem, node, infinity)
    return result


"""
Пребарување низ проблем дефиниран како конечен граф
"""


def distance(a, b):
    """Растојание помеѓу две (x, y) точки."""
    return math.hypot((a[0] - b[0]), (a[1] - b[1]))


class Graph:
    def __init__(self, dictionary=None, directed=True):
        self.dict = dictionary or {}
        self.directed = directed
        if not directed:
            self.make_undirected()
        else:
            # додади празен речник за линковите на оние јазли кои немаат
            # насочени врски и не се дадени како клучеви во речникот
            nodes_no_edges = list({y for x in self.dict.values()
                                   for y in x if y not in self.dict})
            for node in nodes_no_edges:
                self.dict[node] = {}

    def make_undirected(self):
        """Ориентираниот граф претвори го во неориентиран со додавање
        на симетричните ребра."""
        for a in list(self.dict.keys()):
            for (b, dist) in self.dict[a].items():
                self.connect1(b, a, dist)

    def connect(self, node_a, node_b, distance_val=1):
        """Додади ребро од A до B со дадено растојание, а додади го и
        обратното ребро (од B до A) ако графот е неориентиран."""
        self.connect1(node_a, node_b, distance_val)
        if not self.directed:
            self.connect1(node_b, node_a, distance_val)

    def connect1(self, node_a, node_b, distance_val):
        """Додади ребро од A до B со дадено растојание, но само во
        едната насока."""
        self.dict.setdefault(node_a, {})[node_b] = distance_val

    def get(self, a, b=None):
        """Врати растојание придружено на ребро или пак врати речник
        чии елементи се од обликот {јазол : растојание}.
        .get(a,b) го враќа растојанието или пак враќа None
        .get(a) враќа речник со елементи од обликот {јазол : растојание},
            кој може да биде и празен – {}."""
        links = self.dict.get(a)
        if b is None:
            return links
        else:
            return links.get(b)

    def nodes(self):
        """Врати листа од јазлите во графот."""
        return list(self.dict.keys())


def UndirectedGraph(dictionary=None):
    """Изгради Graph во кој што секое ребро (вклучувајќи ги и идните
    ребра) е двонасочно."""
    return Graph(dictionary=dictionary, directed=False)


def RandomGraph(nodes=list(range(10)), min_links=2, width=400, height=300,
                curvature=lambda: random.uniform(1.1, 1.5)):
    """Construct a random graph, with the specified nodes, and random links.
    The nodes are laid out randomly on a (width x height) rectangle.
    Then each node is connected to the min_links nearest neighbors.
    Because inverse links are added, some nodes will have more connections.
    The distance between nodes is the hypotenuse times curvature(),
    where curvature() defaults to a random number between 1.1 and 1.5."""
    g = UndirectedGraph()
    g.locations = {}
    # Build the cities
    for node in nodes:
        g.locations[node] = (random.randrange(width), random.randrange(height))
    # Build roads from each city to at least min_links nearest neighbors.
    for i in range(min_links):
        for node in nodes:
            if len(g.get(node)) < min_links:
                here = g.locations[node]

                def distance_to_node(n):
                    if n is node or g.get(node, n):
                        return math.inf
                    return distance(g.locations[n], here)

                neighbor = nodes.index(min(nodes, key=distance_to_node))
                d = distance(g.locations[neighbor], here) * curvature()
                g.connect(node, neighbor, int(d))
    return g


class GraphProblem(Problem):
    """Проблем на пребарување на граф од еден до друг јазол."""

    def __init__(self, initial, goal, graph):
        super().__init__(initial, goal)
        self.graph = graph

    def actions(self, state):
        """Акциите кај јазол во граф се едноставно - неговите соседи."""
        return list(self.graph.get(state).keys())

    def result(self, state, action):
        """Резултат на одењето кон сосед е самиот тој сосед."""
        return action

    def path_cost(self, c, state1, action, state2):
        return c + (self.graph.get(state1, state2) or math.inf)

    def h(self, node):
        """Функцијата h е праволиниско растојание од состојбата зачувана
        во тековниот јазол до целната состојба."""
        locs = getattr(self.graph, 'locations', None)
        if locs:
            return int(distance(locs[node.state], locs[self.goal]))
        else:
            return math.inf



"""
DRVA NA ODLUKA
"""

def unique_counts(rows):
    """Креирај броење на можни резултати (последната колона
    во секоја редица е класата)

    :param rows: dataset
    :type rows: list
    :return: dictionary of possible classes as keys and count
             as values
    :rtype: dict
    """
    results = {}
    for row in rows:
        # Клацата е последната колона
        r = row[len(row) - 1]
        if r not in results:
            results[r] = 0
        results[r] += 1
    return results


def gini_impurity(rows):
    """Probability that a randomly placed item will
    be in the wrong category

    :param rows: dataset
    :type rows: list
    :return: Gini impurity
    :rtype: float
    """
    total = len(rows)
    counts = unique_counts(rows)
    imp = 0
    for k1 in counts:
        p1 = float(counts[k1]) / total
        for k2 in counts:
            if k1 == k2:
                continue
            p2 = float(counts[k2]) / total
            imp += p1 * p2
    return imp


def entropy(rows):
    """Ентропијата е сума од p(x)log(p(x)) за сите
    можни резултати

    :param rows: податочно множество
    :type rows: list
    :return: вредност за ентропијата
    :rtype: float
    """
    log2 = lambda x: log(x) / log(2)
    results = unique_counts(rows)
    # Пресметка на ентропијата
    ent = 0.0
    for r in results.keys():
        p = float(results[r]) / len(rows)
        ent = ent - p * log2(p)
    return ent


class DecisionNode:
    def __init__(self, col=-1, value=None, results=None, tb=None, fb=None):
        """
        :param col: индексот на колоната (атрибутот) од тренинг множеството
                    која се претставува со оваа инстанца т.е. со овој јазол
        :type col: int
        :param value: вредноста на јазолот според кој се дели дрвото
        :param results: резултати за тековната гранка, вредност (различна
                        од None) само кај јазлите-листови во кои се донесува
                        одлуката.
        :type results: dict
        :param tb: гранка која се дели од тековниот јазол кога вредноста е
                   еднаква на value
        :type tb: DecisionNode
        :param fb: гранка која се дели од тековниот јазол кога вредноста е
                   различна од value
        :type fb: DecisionNode
        """
        self.col = col
        self.value = value
        self.results = results
        self.tb = tb
        self.fb = fb


def compare_numerical(row, column, value):
    """Споредба на вредноста од редицата на посакуваната колона со
    зададена нумеричка вредност

    :param row: дадена редица во податочното множество
    :type row: list
    :param column: индекс на колоната (атрибутот) од тренирачкото множество
    :type column: int
    :param value: вредност на јазелот во согласност со кој се прави
                  поделбата во дрвото
    :type value: int or float
    :return: True ако редицата >= value, инаку False
    :rtype: bool
    """
    return row[column] >= value


def compare_nominal(row, column, value):
    """Споредба на вредноста од редицата на посакуваната колона со
    зададена номинална вредност

    :param row: дадена редица во податочното множество
    :type row: list
    :param column: индекс на колоната (атрибутот) од тренирачкото множество
    :type column: int
    :param value: вредност на јазелот во согласност со кој се прави
                  поделбата во дрвото
    :type value: str
    :return: True ако редицата == value, инаку False
    :rtype: bool
    """
    return row[column] == value


def divide_set(rows, column, value):
    """Поделба на множеството според одредена колона. Може да се справи
    со нумерички или номинални вредности.

    :param rows: тренирачко множество
    :type rows: list(list)
    :param column: индекс на колоната (атрибутот) од тренирачкото множество
    :type column: int
    :param value: вредност на јазелот во зависност со кој се прави поделбата
                  во дрвото за конкретната гранка
    :type value: int or float or str
    :return: поделени подмножества
    :rtype: list, list
    """
    # Направи функција која ни кажува дали редицата е во
    # првата група (True) или втората група (False)
    if isinstance(value, int) or isinstance(value, float):
        # ако вредноста за споредба е од тип int или float
        split_function = compare_numerical
    else:
        # ако вредноста за споредба е од друг тип (string)
        split_function = compare_nominal

    # Подели ги редиците во две подмножества и врати ги
    # за секој ред за кој split_function враќа True
    set1 = [row for row in rows if
            split_function(row, column, value)]
    # за секој ред за кој split_function враќа False
    set2 = [row for row in rows if
            not split_function(row, column, value)]
    return set1, set2


def build_tree(rows, scoref=entropy):
    if len(rows) == 0:
        return DecisionNode()
    current_score = scoref(rows)

    # променливи со кои следиме кој критериум е најдобар
    best_gain = 0.0
    best_criteria = None
    best_sets = None

    column_count = len(rows[0]) - 1
    for col in range(0, column_count):
        # за секоја колона (col се движи во интервалот од 0 до
        # column_count - 1)
        # Следниов циклус е за генерирање на речник од различни
        # вредности во оваа колона
        column_values = {}
        for row in rows:
            column_values[row[col]] = 1
        # за секоја редица се зема вредноста во оваа колона и се
        # поставува како клуч во column_values
        for value in column_values.keys():
            (set1, set2) = divide_set(rows, col, value)

            # Информациона добивка
            p = float(len(set1)) / len(rows)
            gain = current_score - p * scoref(set1) - (1 - p) * scoref(set2)
            if gain > best_gain and len(set1) > 0 and len(set2) > 0:
                best_gain = gain
                best_criteria = (col, value)
                best_sets = (set1, set2)

    # Креирај ги подгранките
    if best_gain > 0:
        true_branch = build_tree(best_sets[0], scoref)
        false_branch = build_tree(best_sets[1], scoref)
        return DecisionNode(col=best_criteria[0], value=best_criteria[1],
                            tb=true_branch, fb=false_branch)
    else:
        return DecisionNode(results=unique_counts(rows))


def print_tree(tree, indent=''):
    # Дали е ова лист јазел?
    if tree.results:
        print(str(tree.results))
    else:
        # Се печати условот
        print(str(tree.col) + ':' + str(tree.value) + '? ')
        # Се печатат True гранките, па False гранките
        print(indent + 'T->', end='')
        print_tree(tree.tb, indent + '  ')
        print(indent + 'F->', end='')
        print_tree(tree.fb, indent + '  ')


def classify(observation, tree):
    if tree.results:
        return tree.results
    else:
        value = observation[tree.col]
        if isinstance(value, int) or isinstance(value, float):
            compare = compare_numerical
        else:
            compare = compare_nominal

        if compare(observation, tree.col, tree.value):
            branch = tree.tb
        else:
            branch = tree.fb

        return classify(observation, branch)



"""
NEVRONSKI MREZHI
"""

# Иницијализација на мрежа
# Ставете фиксни тежини од 0.5 на code.finki.ukim.mk ако постои проблем со random()
def initialize_network(n_inputs, n_hidden, n_outputs):
    """Изградба на мрежата и иницијализација на тежините

    :param n_inputs: број на неврони во влезниот слој
    :type n_inputs: int
    :param n_hidden: број на неврони во скриениот слој
    :type n_hidden: int
    :param n_outputs: број на неврони во излезниот слој
                      (број на класи)
    :type n_outputs: int
    :return: мрежата како листа на слоеви, каде што секој
             слој е речник со клуч 'weights' и нивните вредности
    :rtype: list(list(dict(str, list)))
    """
    network = list()
    hidden_layer = [{'weights': [random() for _ in range(n_inputs + 1)]}
                    for _ in range(n_hidden)]
    network.append(hidden_layer)
    output_layer = [{'weights': [random() for _ in range(n_hidden + 1)]}
                    for _ in range(n_outputs)]
    network.append(output_layer)
    return network


def neuron_calculate(weights, inputs):
    """Пресметување на вредноста за активација на неврон

    :param weights: даден вектор (листа) на тежини
    :type weights: list(float)
    :param inputs: даден вектор (листа) на влезови
    :type inputs: list(float)
    :return: пресметка на невронот
    :rtype: float
    """
    activation = weights[-1]
    for i in range(len(weights) - 1):
        activation += weights[i] * inputs[i]
    return activation


def sigmoid_activation(activation):
    """Sigmoid активациска функција

    :param activation: вредност за активациската функција
    :type activation: float
    :return: вредност добиена од примена на активациската
             функција
    :rtype: float
    """
    return 1.0 / (1.0 + exp(-activation))


def forward_propagate(network, row):
    """Пропагирање нанапред на влезот кон излезот на мрежата

    :param network: дадената мрежа
    :param row: моменталната податочна инстаца
    :return: листа на излезите од последниот слој
    """
    inputs = row
    for layer in network:
        new_inputs = []
        for neuron in layer:
            activation = neuron_calculate(neuron['weights'], inputs)
            neuron['output'] = sigmoid_activation(activation)
            new_inputs.append(neuron['output'])
        inputs = new_inputs
    return inputs


def sigmoid_activation_derivative(output):
    """Пресметување на изводот на излезот од невронот

    :param output: излезни вредности
    :return: вредност на изводот
    """
    return output * (1.0 - output)


def backward_propagate_error(network, expected):
    """Пропагирање на грешката наназад и сочувување во невроните

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param expected: очекувани вредности за излезот
    :type expected: list(int)
    :return: None
    """
    for i in reversed(range(len(network))):
        layer = network[i]
        errors = list()
        if i != len(network) - 1:
            for j in range(len(layer)):
                error = 0.0
                for neuron in network[i + 1]:
                    error += (neuron['weights'][j] * neuron['delta'])
                errors.append(error)
        else:
            for j in range(len(layer)):
                neuron = layer[j]
                errors.append(expected[j] - neuron['output'])
        for j in range(len(layer)):
            neuron = layer[j]
            neuron['delta'] = errors[j] * sigmoid_activation_derivative(neuron['output'])


def update_weights(network, row, l_rate):
    """Ажурирање на тежините на мрежата со грешката

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param row: една инстанца на податоци
    :type row: list
    :param l_rate: рата на учење
    :type l_rate: float
    :return: None
    """
    for i in range(len(network)):
        inputs = row[:-1]
        if i != 0:
            inputs = [neuron['output'] for neuron in network[i - 1]]
        for neuron in network[i]:
            for j in range(len(inputs)):
                neuron['weights'][j] += l_rate * neuron['delta'] * inputs[j]
            neuron['weights'][-1] += l_rate * neuron['delta']


def train_network(network, train, l_rate, n_epoch, n_outputs, verbose=True):
    """Тренирање на мрежата за фиксен број на епохи

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param train: тренирачко множество
    :type train: list
    :param l_rate: рата на учење
    :type l_rate: float
    :param n_epoch: број на епохи
    :type n_epoch: int
    :param n_outputs: број на неврони (класи) во излезниот слој
    :type n_outputs: int
    :param verbose: True за принтање на лог, инаку False
    :type: verbose: bool
    :return: None
    """
    for epoch in range(n_epoch):
        sum_error = 0
        for row in train:
            outputs = forward_propagate(network, row)
            expected = [0] * n_outputs
            expected[row[-1]] = 1
            sum_error += sum([(expected[i] - outputs[i]) ** 2 for i in range(len(expected))])
            backward_propagate_error(network, expected)
            update_weights(network, row, l_rate)
        if verbose:
            print('>epoch=%d, lrate=%.3f, error=%.3f' % (epoch, l_rate, sum_error))


def predict(network, row):
    """Направи предвидување

    :param network: дадена мрежа
    :type network: list(list(dict(str, list)))
    :param row: една податочна инстанца
    :type row: list
    :return: предвидени класи
    """
    outputs = forward_propagate(network, row)
    return outputs.index(max(outputs))




def moveP1(P1):
    ((P11X, P11Y), (P12X, P12Y)), newDir = P1
    if(P11Y == 0 or P11Y == 4):
        newDir *= -1
    return (((P11X, P11Y + newDir), (P12X, P12Y + newDir)), newDir)

def moveP2(P2):
    ((P21X, P21Y), (P22X, P22Y), (P23X, P23Y), (P24X, P24Y)), newDir = P2
    if (P21X == 5 or P21X == 9):
        newDir *= -1
    mY = newDir * -1
    return (((P21X + newDir, P21Y + mY), (P22X + newDir, P22Y + mY), (P23X + newDir, P23Y + mY), (P24X + newDir, P24Y + mY)), newDir)

def moveP3(P3):
    ((P31X, P31Y), (P32X, P32Y)), newDir = P3
    if (P31X == 5 or P31X == 9):
        newDir *= -1
    return (((P31X + newDir, P31Y), (P32X + newDir, P32Y)), newDir)

class PodvizhniPrepreki(Problem):
    def __init__(self, covece, kukja):
        P1 = (((2, 2), (2, 3)), -1)
        P2 = (((7, 2), (7, 3), (8, 2), (8, 3)), -1)
        P3 = (((7, 8), (8, 8)), 1)
        initial_state = (covece, P1, P2, P3)
        self.kukja = kukja
        super().__init__(initial_state)

    def goal_test(self, state):
        return state[0] == self.kukja

    def successor(self, state):
        successors = dict()

        covece, P1, P2, P3 = state
        P1New = moveP1(P1)
        P2New = moveP2(P2)
        P3New = moveP3(P3)
        X, Y = covece

        #Desno
        new_covece = (X, Y + 1)
        if ((X > 4 and Y < 10) or Y < 5) and new_covece not in P1New[0] and new_covece not in P2New[0] and new_covece not in P3New[0]:
            successors["Desno"] = (new_covece, P1New, P2New, P3New)

        #Levo
        new_covece = (X, Y - 1)
        if Y > 0 and new_covece not in P1New[0] and new_covece not in P2New[0] and new_covece not in P3New[0]:
            successors["Levo"] = (new_covece, P1New, P2New, P3New)

        #Gore
        new_covece = (X - 1, Y)
        if ((Y < 6 and X > 0) or X > 5) and new_covece not in P1New[0] and new_covece not in P2New[0] and new_covece not in P3New[0]:
            successors["Gore"] = (new_covece, P1New, P2New, P3New)

        #Dolu
        new_covece = (X + 1, Y)
        if (X < 10) and new_covece not in P1New[0] and new_covece not in P2New[0] and new_covece not in P3New[0]:
            successors["Dolu"] = (new_covece, P1New, P2New, P3New)

        return successors


choveche_redica = int(input())
choveche_kolona = int(input())
kukja_redica = int(input())
kukja_kolona = int(input())


instanca = PodvizhniPrepreki((choveche_redica, choveche_kolona), (kukja_redica, kukja_kolona))
resenie = breadth_first_graph_search(instanca)

print(resenie.solution())