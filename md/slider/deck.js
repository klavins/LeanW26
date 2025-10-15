
class Deck extends React.PureComponent {

  constructor(props) {
    super(props);
    this.switch = this.switch.bind(this);
  }

  switch() {
    if (typeof this.props.switch === 'function') {
      console.log("this.props = ", this.props)
      this.props.switch(this.props.section, this.props.id);
    }
  }

  render() {
    let classes = "deck";
    if (this.props.active) {
      classes += " active-deck";
    }
    return React.createElement(
      'div',
      { onClick: this.switch,
        className: classes },
      (this.props.id + 1) +  '. ' + this.props.title
      //(this.props.section+1) + "." + (this.props.id + 1) +  ': ' + this.props.title
    );
  }

}