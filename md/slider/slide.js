function activate_infoview(slide_index, infoview_index) {
    window.dispatchEvent(new CustomEvent('infoview-click-event', {
        detail: {
          s: slide_index, 
          i: infoview_index
        },
        bubbles: false,
        cancelable: false
    }))
}

class Slide extends React.PureComponent {

  constructor(props) {
    super(props);
    this.props = props;
    this.infoview_list = [];
    this.state = {
        infoview: null // initialize with no active infoview
    }
    this.clear_infoview = this.clear_infoview.bind(this);
  }

  componentDidMount() {
      window.addEventListener('infoview-click-event', this.proof_state);
  }  

  proof_state = (event) => {
    if ( event.detail.s == this.props.id ) {
        this.setState({infoview: event.detail.i });
    }
  };  

  clear_infoview() {
      console.log(this)
      this.setState({infoview: null});
  }

  render() {

    let classes = "markdown-body slide";

    if (this.props.active) {
      classes += " active-slide";
    }


    let html = "";
    if (this.props.id == 0) {
        html = `<div class='first-slide'>
          <div class='course'>EE 598 : Automated Mathematics : W26</div>
          <div class='slide-title'>${this.props.content.split('\n')[0]}</div>
          <div class='author'>
            Prof. Eric Klavins</br>
            Electrical and Computer Engineering</br>
            University of Washington</br>
            Seattle, WA</br>
          </div>
        </div> 
        `
    } 
    else {
        html = this.props.converter.makeHtml(this.props.content);
    }
    let that = this;
    let i = 0;

    html = html.replace(/&lt;proofstate&gt;(.*?)&lt;\/proofstate&gt;/g, function (_, tooltip) {
        that.infoview_list.push({data: tooltip, index: i});
        i++;
        return `<span class="hoverable" onclick="activate_infoview(${that.props.id},${i})" 
                      data-tooltip="show proof state"></span>`;
    });

    return React.createElement(
        'div', 
        { className: classes },
        React.createElement('div', {dangerouslySetInnerHTML: { __html: html } }),
        React.createElement(
            'div',
            { className: "infoview-set-container" },
            this.infoview_list.flatMap((iv,i) => React.createElement(Infoview, { 
                key: iv.index, 
                id: iv.index, 
                data: iv.data,
                active: this.state.infoview == i+1, // why is this i+1 instead of i?
                clear: this.clear_infoview
            }))
        )

    );

  }

}