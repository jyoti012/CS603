class Vehicle {
  private int maxSpeed;
  private String color = "black";

  public Vehicle(int maxSpeed, String color) {
    this.maxSpeed = maxSpeed;
    this.color = color;
  }

  /*
   * method M in superclass
   * precondition: speed > 0
   * postcondition: return true if the speed < maxSpeed, else false
   */
  public boolean canAccelerateTo(int speed) {
    // class invariant for Vehicle: maxSpeed > 0
    return speed > 0 && speed < maxSpeed;
  }

  public int getMaxSpeed() {
    return maxSpeed;
  }

  public String getColor() {
    return color;
  }
}

class Car extends Vehicle {

  public Car(int maxSpeed, String color) {
    super(maxSpeed, color);
  }

  /*
   * overridden method M in subclass
   * precondition: speed > 0 (inherited, not weakened)
   * postcondition: return true if the speed < maxSpeed and speed != 0, else false
   * (strengthened)
   */
  @Override
  public boolean canAccelerateTo(int speed) {
    /*
     * class invariant for Car: speed > 0 AND the Vehicle class invariant (maxSpeed
     * > 0)
     */
    return super.canAccelerateTo(speed) && speed != 0;
  }
}

/**
 * Main
 */
public class Main {

  public static void main(String[] args) {
    Vehicle v = new Vehicle(100, null);
    Car c = new Car(100, "red");

    System.out.println(v.canAccelerateTo(50)); // true
    System.out.println(v.canAccelerateTo(0)); // true
    System.out.println("Car's color: " + c.getColor());
    System.out.println(c.canAccelerateTo(100)); // true
    System.out.println(c.canAccelerateTo(0)); // false
  }
}
