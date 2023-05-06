package src;

public class CreneauHoraireComparable extends CreneauHoraire implements Comparable{

    protected int j, h, m, d;

    public CreneauHoraireComparable(int j, int h, int m, int d) {
        super(j, h, m, d);
    }

    @Override
    public int compareTo (Object o){
       if( o instanceof CreneauHoraire){
           if ( (((CreneauHoraire) o).d - this.d) < 0){
               return -1;
           } else if ((((CreneauHoraire) o).d - this.d) > 0) {
                return 1;
           } else {
               return 0;
           }
        } else {
           throw new IllegalArgumentException("Object must be of Class CreneauHoraire");
       }
    }

}
