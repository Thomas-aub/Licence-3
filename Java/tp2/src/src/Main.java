package src;

public class Main {

    public static void main(String[] args) {
        CreneauHoraire c1 = new CreneauHoraire(87,10,00,1);
        CreneauHoraire c2 = new CreneauHoraire(87,10,00,10);

        // Ex 1.3-4
//        System.out.println(c1==c2);
//        System.out.println(c1.equals(c2));

        // Ex 1.5
//        CreneauHoraire c3 = CreneauHoraire.newCreneauHoraire();
//        System.out.println(c1.equals(c3));

        // Ex 1.6
//        CreneauHoraire c4 = c3.clone();
//        System.out.println(c3.equals(c4));

        // Ex 2.7
        CreneauHoraireComparable c5 = new CreneauHoraireComparable(80, 20, 15, 10);

        try{
            System.out.println(c5.compareTo(c1));
            System.out.println(c5.compareTo(5));
        } catch (IllegalArgumentException e){
            System.out.println(e);
        }


    }


}
