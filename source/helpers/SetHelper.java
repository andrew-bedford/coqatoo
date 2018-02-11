package helpers;

import java.util.HashSet;
import java.util.Set;

public class SetHelper {
    public static <T> Set<T> union(Set<T> setA, Set<T> setB) {
        Set<T> tmp = new HashSet<T>(setA);
        tmp.addAll(setB);
        return tmp;
    }

    public static <T> Set<T> intersection(Set<T> setA, Set<T> setB) {
        Set<T> tmp = new HashSet<T>();
        for (T x : setA) {
            if (setB.contains(x)) {
                tmp.add(x);
            }
        }
        return tmp;
    }

    public static <T> Set<T> difference(Set<T> setA, Set<T> setB) {
        Set<T> tmp = new HashSet<T>(setA);
        tmp.removeAll(setB);
        return tmp;
    }

    public static <T> Set<T> symDifference(Set<T> setA, Set<T> setB) {
        Set<T> tmpA;
        Set<T> tmpB;

        tmpA = union(setA, setB);
        tmpB = intersection(setA, setB);
        return difference(tmpA, tmpB);
    }

    public static <T> boolean isSubset(Set<T> setA, Set<T> setB) {
        return setB.containsAll(setA);
    }

    public static <T> boolean isSuperset(Set<T> setA, Set<T> setB) {
        return setA.containsAll(setB);
    }

    public static <T> String toString(Set<T> set) {
        int numberOfElementsInSet = set.size();
        int i = 0;
        String s = "";
        for (T element : set) {
            i++;
            if (i == numberOfElementsInSet-1) {
                s += element + " and ";
            }
            else if (i == numberOfElementsInSet) {
                s += element;
            }
            else {
                s += element + ", ";
            }
        }

        return s;
    }
}
